-- Prove2me | Theorems.Thm_OAI_PiExponent_InterpolationMatrix_surjective_iff_of_weight_filtered_shift
-- name    : OAI.PiExponent.InterpolationMatrix.surjective_iff_of_weight_filtered_shift
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:33:46.775599+00:00
-- url     : https://prove2.me/theorems/f825b721-cd12-41f0-b89e-f8f6fdfa4ae7
-- title:
--   Filtered transverse shifts preserve interpolation matrix surjectivity
-- statement:
--   Replacing each transverse polynomial by another whose difference has no terms below that transverse variable’s row weight preserves matrix surjectivity. The inverse polynomial shifts preserve the weighted cutoff ideal, including its equality boundary. The statement also covers empty row sets and zero transverse dimension.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison
open OAI.PiExponent
open scoped BigOperators

theorem OAI.PiExponent.InterpolationMatrix.surjective_iff_of_weight_filtered_shift
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ)
    (H : ℝ) (r : Fin m → ℂ) (G G' : Fin m → Polynomial ℂ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hcoeff : ∀ (i : Fin m) (k : ℕ),
      v0 * (k : ℝ) < w i / theta → (G i).coeff k = (G' i).coeff k) :
    Function.Surjective
        (OAI.PiExponent.InterpolationMatrix.matrix K w0 v0 theta w H r G).mulVecLin ↔
      Function.Surjective
        (OAI.PiExponent.InterpolationMatrix.matrix K w0 v0 theta w H r G').mulVecLin := by sorry
