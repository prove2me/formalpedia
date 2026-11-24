-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTheta_Decay_pow_mul_exp_le
-- name    : GlobalTheory.HeckeTheta.Decay.pow_mul_exp_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:06:16.786842+00:00
-- url     : https://prove2.me/theorems/cc38e603-3249-4ace-be41-b308bc3c81aa
-- title:
--   Decay: pow mul exp le
-- statement:
--   The Decay construction uses the pow mul exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L13-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L13-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta

theorem GlobalTheory.HeckeTheta.Decay.pow_mul_exp_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-2 * Real.pi * x ^ 2) ≤ (1 + (k.factorial : ℝ)) * Real.exp (-Real.pi * x ^ 2) := by sorry
