-- Prove2me | Theorems.Thm_GlobalTheory_latticeForm_mul_left
-- name    : GlobalTheory.latticeForm_mul_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:02.543204+00:00
-- url     : https://prove2.me/theorems/c17d223f-7583-428a-ab5b-41f26bd61020
-- title:
--   Global Theory: lattice Form mul left
-- statement:
--   The Global Theory construction uses the lattice Form mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L942-L943
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L942-L943

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

theorem GlobalTheory.latticeForm_mul_left (a u v : ℂ) : latticeForm L (a * u) v = a * latticeForm L u v := by sorry
