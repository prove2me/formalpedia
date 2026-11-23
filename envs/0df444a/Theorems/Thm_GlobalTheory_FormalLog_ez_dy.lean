-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_ez_dy
-- name    : GlobalTheory.FormalLog.ez_dy
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:14.269541+00:00
-- url     : https://prove2.me/theorems/4900ed0e-f708-404c-97c8-211a63de2707
-- title:
--   Formal Log: ez dy
-- statement:
--   The Formal Log construction uses the ez dy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalFamilyConstantCoeffZeroZeroSecondVar.lean#L148-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalFamilyConstantCoeffZeroZeroSecondVar.lean#L148-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)

theorem GlobalTheory.FormalLog.ez_dy (c b : Fin d) : ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F c)) = Jac G c b := by sorry
