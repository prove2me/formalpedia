-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finsum_eq_sum_subtype_of_vanish_outside
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.finsum_eq_sum_subtype_of_vanish_outside
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:19:49.740169+00:00
-- url     : https://prove2.me/theorems/4eff32f7-ff97-4e54-83d8-d4531ce0652c
-- title:
--   Restrict a finitely supported sum to a finite subtype
-- statement:
--   If a complex-valued function vanishes outside a finite set, its `finsum` over the full type equals the ordinary sum over the subtype of that finite set. This isolates the finite-support bookkeeping from the weighted cutoff argument.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.finsum_eq_sum_subtype_of_vanish_outside
    {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℂ)
    (hf : ∀ x, x ∉ s → f x = 0) :
    (∑ᶠ x, f x) = ∑ x : ↥s, f x := by sorry
