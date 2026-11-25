-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_ev_neg
-- name    : GlobalTheory.FormalLog.ev_neg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:16.507849+00:00
-- url     : https://prove2.me/theorems/a58c6670-38b5-5850-b57e-e347d338b217
-- title:
--   Formal Log: ev neg
-- statement:
--   The Formal Log construction uses the ev neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ConstantCoeffEv.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ConstantCoeffEv.lean#L35-L36

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

theorem GlobalTheory.FormalLog.ev_neg {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : ev a (-f) = -ev a f := by sorry
