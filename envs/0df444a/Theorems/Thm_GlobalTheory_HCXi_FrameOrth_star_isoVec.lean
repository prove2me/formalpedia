-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_FrameOrth_star_isoVec
-- name    : GlobalTheory.HCXi.FrameOrth.star_isoVec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:50:42.374799+00:00
-- url     : https://prove2.me/theorems/8ee525ea-a98b-4dcd-a843-c552e66d9e54
-- title:
--   Frame Orth: star iso Vec
-- statement:
--   The Frame Orth construction uses the star iso Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FrameIsotropicOrthonormal.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FrameIsotropicOrthonormal.lean#L35-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.FrameOrth

theorem GlobalTheory.HCXi.FrameOrth.star_isoVec (k r : ℕ) : star (isoVec k r) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    (star (bvec (wI k r 0)) + star (bvec (wI k r (Fin.last k)))) := by sorry
