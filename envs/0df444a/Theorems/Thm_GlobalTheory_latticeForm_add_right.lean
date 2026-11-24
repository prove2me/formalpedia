-- Prove2me | Theorems.Thm_GlobalTheory_latticeForm_add_right
-- name    : GlobalTheory.latticeForm_add_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:17.47602+00:00
-- url     : https://prove2.me/theorems/24f5bb8b-c737-4eed-a193-894b7a219fb5
-- title:
--   Global Theory: lattice Form add right
-- statement:
--   The Global Theory construction uses the lattice Form add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L938-L940
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L938-L940

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

theorem GlobalTheory.latticeForm_add_right (u v v' : ℂ) :
    latticeForm L u (v + v') = latticeForm L u v + latticeForm L u v' := by sorry
