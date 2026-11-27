-- Prove2me | Theorems.Thm_GlobalTheory_logDeriv_weierstrassSigma
-- name    : GlobalTheory.logDeriv_weierstrassSigma
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:22.530607+00:00
-- url     : https://prove2.me/theorems/f6471c5a-7eb8-4ca9-83c6-71b2b4f34eb0
-- title:
--   Global Theory: log Deriv weierstrass Sigma
-- statement:
--   The Global Theory construction uses the log Deriv weierstrass Sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L774-L777
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L774-L777

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

theorem GlobalTheory.logDeriv_weierstrassSigma {z : ℂ} (hz : z ∉ L.lattice) :
    logDeriv (weierstrassSigma L) z = weierstrassZeta L z := by sorry
