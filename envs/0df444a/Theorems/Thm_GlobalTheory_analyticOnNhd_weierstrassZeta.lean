-- Prove2me | Theorems.Thm_GlobalTheory_analyticOnNhd_weierstrassZeta
-- name    : GlobalTheory.analyticOnNhd_weierstrassZeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:42.377137+00:00
-- url     : https://prove2.me/theorems/dc48ff84-a6d0-48df-9c2b-d2768ead35c4
-- title:
--   Global Theory: analytic On Nhd weierstrass Zeta
-- statement:
--   The Global Theory construction uses the analytic On Nhd weierstrass Zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L162-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L162-L166

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

theorem GlobalTheory.analyticOnNhd_weierstrassZeta :
    AnalyticOnNhd ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ := by sorry
