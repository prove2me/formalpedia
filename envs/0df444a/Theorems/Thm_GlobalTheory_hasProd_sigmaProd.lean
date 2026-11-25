-- Prove2me | Theorems.Thm_GlobalTheory_hasProd_sigmaProd
-- name    : GlobalTheory.hasProd_sigmaProd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:02.348362+00:00
-- url     : https://prove2.me/theorems/8425964b-d0b9-46c8-8a88-90ec5f3766ce
-- title:
--   Global Theory: has Prod sigma Prod
-- statement:
--   The Global Theory construction uses the has Prod sigma Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L697-L699
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L697-L699

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

theorem GlobalTheory.hasProd_sigmaProd (z : ℂ) :
    HasProd (fun l : L.lattice => sigmaFactor l z) (sigmaProd L z) := by sorry
