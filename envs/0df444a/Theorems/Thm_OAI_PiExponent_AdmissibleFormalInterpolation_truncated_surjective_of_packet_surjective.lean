-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncated_surjective_of_packet_surjective
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.truncated_surjective_of_packet_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:47:47.434482+00:00
-- url     : https://prove2.me/theorems/6ca72738-711c-401b-912e-3bbdc036e8e0
-- title:
--   Packet surjectivity implies truncated matrix surjectivity
-- statement:
--   Under the stated positivity and truncation bounds, surjectivity of the formal packet coefficient map implies surjectivity of the truncated logarithmic matrix. This is the forward coefficient-transfer direction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.truncated_surjective_of_packet_surjective
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0) :
    Function.Surjective (packetMap K w0 v0 theta w H r) →
      Function.Surjective
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin := by sorry
