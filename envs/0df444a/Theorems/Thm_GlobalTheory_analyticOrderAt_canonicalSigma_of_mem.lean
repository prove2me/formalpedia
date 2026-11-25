-- Prove2me | Theorems.Thm_GlobalTheory_analyticOrderAt_canonicalSigma_of_mem
-- name    : GlobalTheory.analyticOrderAt_canonicalSigma_of_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:22.364879+00:00
-- url     : https://prove2.me/theorems/1e9e31d7-fbd5-59c4-96f3-525217a7d508
-- title:
--   Global Theory: analytic Order At canonical Sigma of mem
-- statement:
--   The Global Theory construction uses the analytic Order At canonical Sigma of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1028-L1034
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1028-L1034

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

theorem GlobalTheory.analyticOrderAt_canonicalSigma_of_mem {w : ℂ} (hw : w ∈ L.lattice) :
    analyticOrderAt (canonicalSigma L) w = 1 := by sorry
