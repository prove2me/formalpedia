-- Prove2me | Theorems.Thm_GlobalTheory_analyticOrderAt_weierstrassSigma_of_notMem
-- name    : GlobalTheory.analyticOrderAt_weierstrassSigma_of_notMem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:30.430218+00:00
-- url     : https://prove2.me/theorems/c167a7d3-655b-599e-8fef-ba583cfb32e6
-- title:
--   Global Theory: analytic Order At weierstrass Sigma of not Mem
-- statement:
--   The Global Theory construction uses the analytic Order At weierstrass Sigma of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L928-L930
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L928-L930

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

theorem GlobalTheory.analyticOrderAt_weierstrassSigma_of_notMem {z : ℂ} (hz : z ∉ L.lattice) :
    analyticOrderAt (weierstrassSigma L) z = 0 := by sorry
