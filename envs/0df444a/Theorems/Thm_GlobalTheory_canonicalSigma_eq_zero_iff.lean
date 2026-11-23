-- Prove2me | Theorems.Thm_GlobalTheory_canonicalSigma_eq_zero_iff
-- name    : GlobalTheory.canonicalSigma_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:29.496606+00:00
-- url     : https://prove2.me/theorems/af0544fc-17cb-4435-8afb-982f1422291f
-- title:
--   Global Theory: canonical Sigma eq zero iff
-- statement:
--   The Global Theory construction uses the canonical Sigma eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1010-L1011
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1010-L1011

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

theorem GlobalTheory.canonicalSigma_eq_zero_iff {z : ℂ} : canonicalSigma L z = 0 ↔ z ∈ L.lattice := by sorry
