-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_pderiv_first_ev_second_point_eq_zero
-- name    : GlobalTheory.FormalLog.pderiv_first_ev_second_point_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:36:57.007429+00:00
-- url     : https://prove2.me/theorems/9bc5ef4a-6639-4586-9a05-d8fa907065e5
-- title:
--   Formal Log: pderiv first ev second point eq zero
-- statement:
--   The Formal Log construction uses the pderiv first ev second point eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PderivSecondEvFirstPointEqZero.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PderivSecondEvFirstPointEqZero.lean#L49-L50

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

theorem GlobalTheory.FormalLog.pderiv_first_ev_second_point_eq_zero (h : PS k 1 d) (a : Fin d) : pderiv k ((0 : Fin 2), a) (ev (n := 2) ![pt k d 1] h) = 0 := by sorry
