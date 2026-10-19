-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_iUnion_finset_eq_sum
-- name    : OAI.PiExponent.DeterminantContradiction.volume_iUnion_finset_eq_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:12:48.426797+00:00
-- url     : https://prove2.me/theorems/abc14aaa-070e-41db-ab7f-fe0c1762baa4
-- title:
--   Volume of a finite disjoint union
-- statement:
--   For a finite family of measurable, pairwise-disjoint sets in finite-dimensional real space, the volume of their union is the sum of their volumes.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.volume_iUnion_finset_eq_sum
    {m : ℕ} {ι : Type} [DecidableEq ι] (S : Finset ι)
    (A : ι → Set (Fin m → ℝ))
    (hmeas : ∀ a ∈ S, MeasurableSet (A a))
    (hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (A a) (A b)) :
    MeasureTheory.volume (⋃ a ∈ S, A a) =
      ∑ a ∈ S, MeasureTheory.volume (A a) := by sorry
