-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_FrameOrth_fvec_castSucc
-- name    : GlobalTheory.HCXi.FrameOrth.fvec_castSucc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:56:05.928253+00:00
-- url     : https://prove2.me/theorems/b38fd037-16e8-4b3a-af0f-a8bfb41b06b6
-- title:
--   Frame Orth: fvec cast Succ
-- statement:
--   The Frame Orth construction uses the fvec cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FrameIsotropicOrthonormal.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FrameIsotropicOrthonormal.lean#L20-L22

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

theorem GlobalTheory.HCXi.FrameOrth.fvec_castSucc (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    fvec k r z a.castSucc = bvec (eI k r a) := by sorry
