-- Prove2me | Theorems.Thm_GlobalTheory_IsHomothetic_sigmaProd_mul
-- name    : GlobalTheory.IsHomothetic.sigmaProd_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:09.451847+00:00
-- url     : https://prove2.me/theorems/fdf55e8a-a640-4ba9-b968-90ddbdaf6f60
-- title:
--   Is Homothetic: sigma Prod mul
-- statement:
--   The Is Homothetic construction uses the sigma Prod mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L779-L783
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L779-L783

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

theorem GlobalTheory.IsHomothetic.sigmaProd_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') (z : ℂ) :
    sigmaProd L' (c * z) = sigmaProd L z := by sorry
