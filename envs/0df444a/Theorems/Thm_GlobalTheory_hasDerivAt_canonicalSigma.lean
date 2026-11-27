-- Prove2me | Theorems.Thm_GlobalTheory_hasDerivAt_canonicalSigma
-- name    : GlobalTheory.hasDerivAt_canonicalSigma
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:08.201258+00:00
-- url     : https://prove2.me/theorems/6eebd71c-82d6-4f94-b766-6a5c8932c1a1
-- title:
--   Global Theory: has Deriv At canonical Sigma
-- statement:
--   The Global Theory construction uses the has Deriv At canonical Sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1023-L1026
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1023-L1026

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

theorem GlobalTheory.hasDerivAt_canonicalSigma {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt (canonicalSigma L)
    ((weierstrassZeta L z - sTwo L * z) * canonicalSigma L z) z := by sorry
