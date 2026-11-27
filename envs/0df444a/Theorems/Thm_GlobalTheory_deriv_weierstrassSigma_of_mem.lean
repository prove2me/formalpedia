-- Prove2me | Theorems.Thm_GlobalTheory_deriv_weierstrassSigma_of_mem
-- name    : GlobalTheory.deriv_weierstrassSigma_of_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:26.216018+00:00
-- url     : https://prove2.me/theorems/6ce52073-4580-5667-a8b7-bb94552b4adc
-- title:
--   Global Theory: deriv weierstrass Sigma of mem
-- statement:
--   The Global Theory construction uses the deriv weierstrass Sigma of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L918-L921
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L918-L921

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

theorem GlobalTheory.deriv_weierstrassSigma_of_mem {w : ℂ} (hw : w ∈ L.lattice) :
    deriv (weierstrassSigma L) w = sigmaSign L w * cexp (quasiPeriod L w * (w / 2)) := by sorry
