-- Prove2me | Theorems.Thm_OAI_PiExponent_InterpolationMatrix_weight_filtered_shift_row_equivalence
-- name    : OAI.PiExponent.InterpolationMatrix.weight_filtered_shift_row_equivalence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:09:45.144998+00:00
-- url     : https://prove2.me/theorems/9daefd40-dd6a-4506-9c84-ac9dd2453071
-- title:
--   Filtered shifts induce an invertible row transformation
-- statement:
--   Construct an invertible row transformation relating the two interpolation matrices. This removes the finite filtered-substitution step from the parent. A proof route expands the polynomial entries and proves that each changed term preserves or raises row weight; the reverse shift gives the inverse transformation. The exact boundary is controlled by the strict inequality in the row simplex, so equality at the coefficient threshold must be retained. The remaining core is establishing this triangularity for the defined row indices and matrix entries.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison
open OAI.PiExponent
open scoped BigOperators

theorem OAI.PiExponent.InterpolationMatrix.weight_filtered_shift_row_equivalence
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ)
    (H : ℝ) (r : Fin m → ℂ) (G G' : Fin m → Polynomial ℂ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hcoeff : ∀ (i : Fin m) (k : ℕ),
      v0 * (k : ℝ) < w i / theta → (G i).coeff k = (G' i).coeff k) :
    ∃ U : Matrix
        (OAI.PiExponent.InterpolationMatrix.Row K v0 theta w H)
        (OAI.PiExponent.InterpolationMatrix.Row K v0 theta w H) ℂ,
      Function.Bijective U.mulVecLin ∧
      OAI.PiExponent.InterpolationMatrix.matrix K w0 v0 theta w H r G =
        U * OAI.PiExponent.InterpolationMatrix.matrix K w0 v0 theta w H r G' := by sorry
