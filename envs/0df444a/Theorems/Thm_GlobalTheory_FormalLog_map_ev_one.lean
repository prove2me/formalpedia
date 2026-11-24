-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_map_ev_one
-- name    : GlobalTheory.FormalLog.map_ev_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:34:57.217461+00:00
-- url     : https://prove2.me/theorems/e0cb98d2-930a-4fc2-b305-1ebd44f2bf30
-- title:
--   Formal Log: map ev one
-- statement:
--   The Formal Log construction uses the map ev one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalFamilyConstantCoeffZeroZeroSecondVar.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalFamilyConstantCoeffZeroZeroSecondVar.lean#L64-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
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

theorem GlobalTheory.FormalLog.map_ev_one {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) :
    (1 : Matrix (Fin d) (Fin d) (PS k m d)).map (ev a) = 1 := by sorry
