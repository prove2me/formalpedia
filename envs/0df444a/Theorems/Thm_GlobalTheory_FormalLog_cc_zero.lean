-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_cc_zero
-- name    : GlobalTheory.FormalLog.cc_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:57.328186+00:00
-- url     : https://prove2.me/theorems/9dc133b3-e1d4-4ff3-ac7a-6d6c086588ab
-- title:
--   Formal Log: cc zero
-- statement:
--   The Formal Log construction uses the cc zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean#L18-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
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

theorem GlobalTheory.FormalLog.cc_zero {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt k n d) i) = 0 := by sorry
