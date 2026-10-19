-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_box_packing_bound
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_lattice_box_packing_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:47:40.00616+00:00
-- url     : https://prove2.me/theorems/af082774-46be-4178-a723-66187388d626
-- title:
--   Weighted lattice-point bound by box packing
-- statement:
--   For any finite set of nonnegative integer vectors whose weighted coordinate sums are at most a nonnegative cutoff, its cardinality is at most the volume bound obtained by expanding the cutoff by the sum of the positive weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weighted_lattice_box_packing_bound
    (m : ℕ) (s : Finset (Fin m → ℕ)) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T)
    (hs : ∀ a ∈ s, ∑ i : Fin m, w i * (a i : ℝ) ≤ T) :
    (s.card : ℝ) ≤
      (T + ∑ i : Fin m, w i) ^ m /
        ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i) := by sorry
