-- Prove2me | Theorems.Thm_GlobalTheory_IsHomothetic_sigmaSign_mul
-- name    : GlobalTheory.IsHomothetic.sigmaSign_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:33.536176+00:00
-- url     : https://prove2.me/theorems/93976f7f-8600-445a-b5b8-4d9889f497ea
-- title:
--   Is Homothetic: sigma Sign mul
-- statement:
--   The Is Homothetic construction uses the sigma Sign mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L821-L825
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L821-L825

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)

theorem GlobalTheory.IsHomothetic.sigmaSign_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') (w : ℂ) :
    sigmaSign L' (c * w) = sigmaSign L w := by sorry
