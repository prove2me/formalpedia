-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_ev_pt
-- name    : GlobalTheory.FormalLog.ev_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:08.89166+00:00
-- url     : https://prove2.me/theorems/8c81f433-583c-4d04-9f7b-b04bd93a48a7
-- title:
--   Formal Log: ev pt
-- statement:
--   The Formal Log construction uses the ev pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ConstantCoeffEv.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ConstantCoeffEv.lean#L65-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
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
variable {k : Type} [CommRing k] {d m n : ℕ}

theorem GlobalTheory.FormalLog.ev_pt (f : PS k m d) : ev (fun j => pt k (n := m) d j) f = f := by sorry
