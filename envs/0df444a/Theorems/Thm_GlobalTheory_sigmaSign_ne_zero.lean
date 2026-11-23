-- Prove2me | Theorems.Thm_GlobalTheory_sigmaSign_ne_zero
-- name    : GlobalTheory.sigmaSign_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:14.149929+00:00
-- url     : https://prove2.me/theorems/624bdc31-1de5-4fb4-aa9e-9b77d4d5786f
-- title:
--   Global Theory: sigma Sign ne zero
-- statement:
--   The Global Theory construction uses the sigma Sign ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L807-L808
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L807-L808

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

theorem GlobalTheory.sigmaSign_ne_zero (w : ℂ) : sigmaSign L w ≠ 0 := by sorry
