-- Prove2me | Theorems.Thm_GlobalTheory_IsHomothetic_weierstrassSigma_mul
-- name    : GlobalTheory.IsHomothetic.weierstrassSigma_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:39.550293+00:00
-- url     : https://prove2.me/theorems/dfcf88dc-26b4-4db1-b9fd-efe465385c87
-- title:
--   Is Homothetic: weierstrass Sigma mul
-- statement:
--   The Is Homothetic construction uses the weierstrass Sigma mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L785-L787
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L785-L787

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

theorem GlobalTheory.IsHomothetic.weierstrassSigma_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (z : ℂ) : weierstrassSigma L' (c * z) = c * weierstrassSigma L z := by sorry
