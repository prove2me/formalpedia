-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncated_matrix_of_packets
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.truncated_matrix_of_packets
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-12T19:59:29.652993+00:00
-- url     : https://prove2.me/theorems/d0a8faa3-300d-4f2a-b488-ca09908098e7
-- title:
--   Transfer formal packet interpolation to a truncated logarithmic matrix
-- statement:
--   For arbitrary positive row and column weights and arbitrary complex centers, surjectivity of formal logarithmic coefficient packets implies surjectivity of the truncated-log matrix whenever each truncation order satisfies wᵢ/θ ≤ Tᵢv₀.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.truncated_matrix_of_packets {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i) (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (hpacket : Function.Surjective (packetMap K w0 v0 theta w H r)) :
    Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin := by sorry
