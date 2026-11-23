import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_759

def E : List (ℕ × ℕ) := [(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 4), (4, 1), (4, 5), (5, 4)]

def G : SimpleGraph (Fin 6) where
  Adj i j := (i.val, j.val) ∈ E
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

theorem adj_iff (i j : Fin 6) : G.Adj i j ↔ (i.val, j.val) ∈ E := Iff.rfl

def dec : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable ((i.val, j.val) ∈ E))

theorem hasEdge : ∃ i j : Fin 6, G.Adj i j := ⟨0, 1, (adj_iff 0 1).mpr (by decide)⟩

theorem cover04 : ∀ i j : Fin 6, G.Adj i j → i ∈ ({0, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 4} : Finset (Fin 6)) := by
  intro i j h
  rw [adj_iff] at h
  revert i j
  decide

theorem uncovered : ∀ v : Fin 6, ∃ i j : Fin 6, (i.val, j.val) ∈ E ∧ i ≠ v ∧ j ≠ v := by decide

theorem cover2 : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T hT
  by_contra h
  obtain ⟨v, hv⟩ : ∃ v, T ⊆ {v} := Finset.card_le_one_iff_subset_singleton.mp (by omega)
  obtain ⟨i, j, hij, hi, hj⟩ := uncovered v
  rcases hT i j ((adj_iff i j).mpr hij) with h | h
  · exact hi (Finset.mem_singleton.mp (hv h))
  · exact hj (Finset.mem_singleton.mp (hv h))

theorem reach0 : ∀ v : Fin 6, G.Reachable 0 v := by
  have a01 : G.Adj 0 1 := (adj_iff 0 1).mpr (by decide)
  have a02 : G.Adj 0 2 := (adj_iff 0 2).mpr (by decide)
  have a03 : G.Adj 0 3 := (adj_iff 0 3).mpr (by decide)
  have a14 : G.Adj 1 4 := (adj_iff 1 4).mpr (by decide)
  have a45 : G.Adj 4 5 := (adj_iff 4 5).mpr (by decide)
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact a01.reachable
  · exact a02.reachable
  · exact a03.reachable
  · exact a01.reachable.trans a14.reachable
  · exact (a01.reachable.trans a14.reachable).trans a45.reachable

theorem connected : G.Connected :=
  { preconnected := fun u v => (reach0 u).symm.trans (reach0 v) }

end PEqualNP.Outside.L_meta_759

open PEqualNP.Outside.L_meta_759 in
theorem PEqualNP.Outside.L_meta_759 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  intro s
  letI : DecidableRel G.Adj := dec
  have card5 : G.edgeFinset.card = 5 := by decide
  have tree : G.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨connected, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, card5]
    rfl
  have hfun : (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true))
      = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) := by
    funext x
    have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
    generalize x 0 = a
    generalize x 1 = b
    generalize x 2 = c
    generalize x 3 = d
    generalize x 4 = e
    generalize x 5 = f
    revert a b c d e f
    decide
  rw [← hfun]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 6 2 s G tree.isAcyclic hasEdge cover2 h
    rw [card5] at this
    omega
  · intro hs
    obtain ⟨C, h1, h2, h3⟩ := PEqualNP.MetaComplexity.L105 6 G {0, 4} hasEdge cover04
    rw [card5] at h2
    exact ⟨C, h1, by simp at h2; omega, h3⟩
