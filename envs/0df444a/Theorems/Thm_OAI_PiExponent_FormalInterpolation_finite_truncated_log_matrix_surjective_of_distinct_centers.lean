-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_truncated_log_matrix_surjective_of_distinct_centers
-- name    : OAI.PiExponent.FormalInterpolation.finite_truncated_log_matrix_surjective_of_distinct_centers
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-13T06:05:49.505235+00:00
-- url     : https://prove2.me/theorems/6758a74f-a924-413a-a2a4-f85874873f79
-- title:
--   Finite truncated-log interpolation matrix is surjective at distinct centers
-- statement:
--   For any column weight and truncation data, distinct center profiles make the finite truncated-log interpolation matrix surjective onto the row packet space.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finite_truncated_log_matrix_surjective_of_distinct_centers
    {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
    (r : Fin m → Complex) (T : Fin m → Nat)
    (hcenters : Function.Injective
      (fun j : Fin K => fun i : Fin m => (j.val : Complex) * r i)) :
    Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin := by sorry
