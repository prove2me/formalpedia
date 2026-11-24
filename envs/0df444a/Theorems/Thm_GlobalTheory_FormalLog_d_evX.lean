-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_d_evX
-- name    : GlobalTheory.FormalLog.d_evX
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:34:52.489804+00:00
-- url     : https://prove2.me/theorems/33e81900-530d-47c8-a4d6-e2a9bd28952b
-- title:
--   Formal Log: d ev X
-- statement:
--   The Formal Log construction uses the d ev X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PderivSecondEvFirstPointEqZero.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PderivSecondEvFirstPointEqZero.lean#L44-L47

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

theorem GlobalTheory.FormalLog.d_evX (h : PS k 1 d) (a : Fin d) :
    pderiv k ((0 : Fin 2), a) (ev (n := 2) ![pt k d 0] h) = ev (n := 2) ![pt k d 0] (pderiv k ((0 : Fin 1), a) h) := by sorry
