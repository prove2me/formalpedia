-- Prove2me | Theorems.Thm_GlobalTheory_quasiPeriod_eq_two_mul
-- name    : GlobalTheory.quasiPeriod_eq_two_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:50:07.805803+00:00
-- url     : https://prove2.me/theorems/2e78ce6f-da8b-41aa-9e40-3e4dd60715fb
-- title:
--   Global Theory: quasi Period eq two mul
-- statement:
--   The Global Theory construction uses the quasi Period eq two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L266-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L266-L270

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

theorem GlobalTheory.quasiPeriod_eq_two_mul {w : ℂ} (hw : w ∈ L.lattice) (hw2 : w / 2 ∉ L.lattice) :
    quasiPeriod L w = 2 * weierstrassZeta L (w / 2) := by sorry
