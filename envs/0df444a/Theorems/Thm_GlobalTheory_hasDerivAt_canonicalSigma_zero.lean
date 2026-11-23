-- Prove2me | Theorems.Thm_GlobalTheory_hasDerivAt_canonicalSigma_zero
-- name    : GlobalTheory.hasDerivAt_canonicalSigma_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:10.851802+00:00
-- url     : https://prove2.me/theorems/403bbc3e-4d59-49e6-8a17-4b900e8b97fa
-- title:
--   Global Theory: has Deriv At canonical Sigma zero
-- statement:
--   The Global Theory construction uses the has Deriv At canonical Sigma zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1020-L1021
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1020-L1021

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

theorem GlobalTheory.hasDerivAt_canonicalSigma_zero : HasDerivAt (canonicalSigma L) 1 0 := by sorry
