-- Prove2me | Theorems.Thm_GlobalTheory_IsHomothetic_canonicalSigma_mul
-- name    : GlobalTheory.IsHomothetic.canonicalSigma_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:21:19.684805+00:00
-- url     : https://prove2.me/theorems/27f3370e-acaa-4209-a07b-825ef9c0c2bc
-- title:
--   Is Homothetic: canonical Sigma mul
-- statement:
--   The Is Homothetic construction uses the canonical Sigma mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1036-L1041
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1036-L1041

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

theorem GlobalTheory.IsHomothetic.canonicalSigma_mul {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L')
    (z : ℂ) : canonicalSigma L' (c * z) = c * canonicalSigma L z := by sorry
