-- Prove2me | Theorems.Thm_GlobalTheory_abs_im_latticeForm
-- name    : GlobalTheory.abs_im_latticeForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:45.856571+00:00
-- url     : https://prove2.me/theorems/9fdeb091-a402-4fdc-9eb6-2ab82028214b
-- title:
--   Global Theory: abs im lattice Form
-- statement:
--   The Global Theory construction uses the abs im lattice Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L965-L967
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L965-L967

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

theorem GlobalTheory.abs_im_latticeForm : |(latticeForm L L.ω₂ L.ω₁).im| = 1 := by sorry
