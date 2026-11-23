-- Prove2me | Theorems.Thm_GlobalTheory_conj_latticeForm
-- name    : GlobalTheory.conj_latticeForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:46.556373+00:00
-- url     : https://prove2.me/theorems/e9b1d341-b824-4309-bd6b-9ffd1411ab34
-- title:
--   Global Theory: conj lattice Form
-- statement:
--   The Global Theory construction uses the conj lattice Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L952-L953
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L952-L953

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

theorem GlobalTheory.conj_latticeForm (u v : ℂ) : conj (latticeForm L u v) = latticeForm L v u := by sorry
