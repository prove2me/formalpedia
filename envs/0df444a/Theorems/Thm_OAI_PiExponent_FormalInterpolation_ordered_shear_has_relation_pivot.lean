-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_ordered_shear_has_relation_pivot
-- name    : OAI.PiExponent.FormalInterpolation.ordered_shear_has_relation_pivot
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:32:42.130711+00:00
-- url     : https://prove2.me/theorems/e1be9b36-02df-4c99-925e-79581fd41bc4
-- title:
--   Ordered basis exclusion for an invertible shear produces a relation pivot
-- statement:
--   This isolates finite linear algebra over an arbitrary field, independently of polynomial ideals and derivations. The shear is invertible because t≠0, so the two spans coincide and their bases have equal cardinality. If a positive u-column is nonzero, choose the largest such index i and extend its singleton to a column basis A. Every higher column vanishes in both families, so no basis contains a higher index. Exclusion consequently forces every v-basis to contain i. A relation with nonzero coefficient at i would express v_i using the remaining columns; extracting a basis from those columns contradicts this requirement. This proves the pivot property. Basis extension can use the inspected `LinearIndepOn.linearIndepOn_extend` infrastructure. If every positive column vanishes, hnonzero forces u₀≠0 and hence v₀≠0, giving pivot zero directly. This includes m=0. Both t≠0 and hnonzero are essential and retained.

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.ordered_shear_has_relation_pivot
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m : Nat} (u v : Fin (m + 1) → V) (t : K) (ht : t ≠ 0)
    (hzero : v 0 = t • u 0 + ∑ j : Fin m, u j.succ)
    (hsucc : ∀ j : Fin m, v j.succ = u j.succ)
    (hnonzero : ∃ i, u i ≠ 0)
    (hexclusion :
      ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
        (LinearIndependent K (fun i : A => u i) ∧
          Submodule.span K (Set.range (fun i : A => u i)) =
            Submodule.span K (Set.range u)) →
        (LinearIndependent K (fun i : B => v i) ∧
          Submodule.span K (Set.range (fun i : B => v i)) =
            Submodule.span K (Set.range v)) →
        ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
          (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ i : Fin (m + 1),
      ∀ a : Fin (m + 1) → K, (∑ j, a j • v j) = 0 → a i = 0 := by
  sorry
