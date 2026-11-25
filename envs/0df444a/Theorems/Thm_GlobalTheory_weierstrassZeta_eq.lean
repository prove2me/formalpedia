-- Prove2me | Theorems.Thm_GlobalTheory_weierstrassZeta_eq
-- name    : GlobalTheory.weierstrassZeta_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:51:19.120207+00:00
-- url     : https://prove2.me/theorems/dd940d66-867c-536e-a990-04e35054e72f
-- title:
--   Global Theory: weierstrass Zeta eq
-- statement:
--   The Global Theory construction uses the weierstrass Zeta eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L109-L113

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

theorem GlobalTheory.weierstrassZeta_eq (z : ℂ) : weierstrassZeta L z = 1 / z +
    ∑' l : L.lattice, if (l : ℂ) = 0 then 0 else (1 / (z - l) + 1 / l + z / l ^ 2) := by sorry
