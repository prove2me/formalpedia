-- Prove2me | Theorems.Thm_GlobalTheory_HCA_SolSub_hasCompactSupport_dw
-- name    : GlobalTheory.HCA.SolSub.hasCompactSupport_dw
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:59:14.197425+00:00
-- url     : https://prove2.me/theorems/49ac3c50-e6c1-4b00-acbc-83714f838105
-- title:
--   Sol Sub: has Compact Support dw
-- statement:
--   The Sol Sub construction uses the has Compact Support dw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AestronglyMeasurableExtendByZeroOffSubset.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AestronglyMeasurableExtendByZeroOffSubset.lean#L21-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.HCA GlobalTheory.HCA.SolSub
variable {d : ℕ}

theorem GlobalTheory.HCA.SolSub.hasCompactSupport_dw {f : E d → ℂ} (hf : HasCompactSupport f) :
    ∀ w : List (Fin d), HasCompactSupport (dw w f)
  := by sorry
