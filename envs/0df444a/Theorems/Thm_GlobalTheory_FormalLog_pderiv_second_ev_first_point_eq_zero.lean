-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_pderiv_second_ev_first_point_eq_zero
-- name    : GlobalTheory.FormalLog.pderiv_second_ev_first_point_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:05.656052+00:00
-- url     : https://prove2.me/theorems/4b0a2985-4eb7-4a9a-aa28-caf6e6c951fc
-- title:
--   Formal Log: pderiv second ev first point eq zero
-- statement:
--   The Formal Log construction uses the pderiv second ev first point eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PderivSecondEvFirstPointEqZero.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PderivSecondEvFirstPointEqZero.lean#L52-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)

theorem GlobalTheory.FormalLog.pderiv_second_ev_first_point_eq_zero (h : PS k 1 d) (b : Fin d) : pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 0] h) = 0 := by sorry
