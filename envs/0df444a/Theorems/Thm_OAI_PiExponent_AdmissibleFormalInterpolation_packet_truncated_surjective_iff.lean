-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_packet_truncated_surjective_iff
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.packet_truncated_surjective_iff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:41:10.41622+00:00
-- url     : https://prove2.me/theorems/0b9edfc9-ac14-4f8d-bb6d-9c8b50e1f24b
-- title:
--   Surjectivity is preserved by logarithmic truncation
-- statement:
--   Under the stated positive weights and truncation bounds, surjectivity of the formal packet coefficient map is equivalent to surjectivity of the truncated logarithmic matrix. The equivalence captures preservation of rank under a triangular change of coefficients on the strict weighted row simplex.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.packet_truncated_surjective_iff
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0) :
    Function.Surjective (packetMap K w0 v0 theta w H r) ↔
      Function.Surjective
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin := by sorry
