-- Prove2me | Theorems.Thm_GlobalTheory_analyticOrderAt_weierstrassSigma_of_mem
-- name    : GlobalTheory.analyticOrderAt_weierstrassSigma_of_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:33.354858+00:00
-- url     : https://prove2.me/theorems/bdb8d7fb-ba42-43d7-a7b5-1a44ed5d79fe
-- title:
--   Global Theory: analytic Order At weierstrass Sigma of mem
-- statement:
--   The Global Theory construction uses the analytic Order At weierstrass Sigma of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L923-L926
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L923-L926

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

theorem GlobalTheory.analyticOrderAt_weierstrassSigma_of_mem {w : ℂ} (hw : w ∈ L.lattice) :
    analyticOrderAt (weierstrassSigma L) w = 1 := by sorry
