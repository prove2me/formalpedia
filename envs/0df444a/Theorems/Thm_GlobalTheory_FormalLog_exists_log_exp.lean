-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_exists_log_exp
-- name    : GlobalTheory.FormalLog.exists_log_exp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:02.862029+00:00
-- url     : https://prove2.me/theorems/94d0e219-e062-498a-8b52-5b2ea9ab27be
-- title:
--   Formal Log: exists log exp
-- statement:
--   The Formal Log construction uses the exists log exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOrSingleOfDegreeLeOne.lean#L24-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOrSingleOfDegreeLeOne.lean#L24-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalCompApplyEqMvPowerSeriesSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOrSingleOfDegreeLeOne
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt

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

theorem GlobalTheory.FormalLog.exists_log_exp :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d), ∃ lg ex : Pt k 1 d, (∀ i (μ : Fin 1 × Fin d →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS k 1 d)) ∧ (∀ i, ev (n := 2) ![addOf G.F (pt k d 0) (pt k d 1)] (lg i) = ev (n := 2) ![pt k d 0] (lg i) + ev (n := 2) ![pt k d 1] (lg i)) ∧ (∀ i, MvPowerSeries.constantCoeff (ex i) = 0) ∧ comp1 lg ex = pt k d 0 ∧ comp1 ex lg = pt k d 0 := by sorry
