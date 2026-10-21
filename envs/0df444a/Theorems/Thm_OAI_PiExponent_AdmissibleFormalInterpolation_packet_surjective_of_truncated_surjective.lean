-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_packet_surjective_of_truncated_surjective
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.packet_surjective_of_truncated_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:47:17.685716+00:00
-- url     : https://prove2.me/theorems/222be3f0-0e2f-40ed-9a88-3c5314b7d716
-- title:
--   Truncated matrix surjectivity implies packet surjectivity
-- statement:
--   Under the same hypotheses, surjectivity of the truncated logarithmic matrix implies surjectivity of the formal packet coefficient map. This is the reverse coefficient-transfer direction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.packet_surjective_of_truncated_surjective
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0) :
    Function.Surjective
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin →
      Function.Surjective (packetMap K w0 v0 theta w H r) := by sorry
