-- Prove2me | Theorems.Thm_GlobalTheory_IsHomothetic_latticeForm_mul
-- name    : GlobalTheory.IsHomothetic.latticeForm_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:16.992526+00:00
-- url     : https://prove2.me/theorems/d0774226-21fe-47e9-8118-2cb9cf706663
-- title:
--   Is Homothetic: lattice Form mul
-- statement:
--   The Is Homothetic construction uses the lattice Form mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L987-L994
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L987-L994

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

theorem GlobalTheory.IsHomothetic.latticeForm_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (u v : ℂ) : latticeForm L' (c * u) (c * v) = latticeForm L u v := by sorry
