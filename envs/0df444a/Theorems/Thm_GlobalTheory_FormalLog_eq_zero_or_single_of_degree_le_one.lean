-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_eq_zero_or_single_of_degree_le_one
-- name    : GlobalTheory.FormalLog.eq_zero_or_single_of_degree_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:36:10.504862+00:00
-- url     : https://prove2.me/theorems/56a4a70d-6bc6-475a-841d-1340a355e5cd
-- title:
--   Formal Log: eq zero or single of degree le one
-- statement:
--   The Formal Log construction uses the eq zero or single of degree le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOrSingleOfDegreeLeOne.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOrSingleOfDegreeLeOne.lean#L10-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalCompApplyEqMvPowerSeriesSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOrSingleOfDegreeLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog

theorem GlobalTheory.FormalLog.eq_zero_or_single_of_degree_le_one {σ : Type} (μ : σ →₀ ℕ) (h : μ.degree ≤ 1) :
    μ = 0 ∨ ∃ s, μ = Finsupp.single s 1 := by sorry
