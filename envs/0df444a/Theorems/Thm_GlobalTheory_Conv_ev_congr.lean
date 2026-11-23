-- Prove2me | Theorems.Thm_GlobalTheory_Conv_ev_congr
-- name    : GlobalTheory.Conv.ev_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:54.171859+00:00
-- url     : https://prove2.me/theorems/ed33b6af-084d-4896-ae0a-e3f79f8d41bf
-- title:
--   Conv: ev congr
-- statement:
--   The Conv construction uses the ev congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L125-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology
open Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (eTwoPi SumsAt)
noncomputable section
open GlobalTheory GlobalTheory.Conv

theorem GlobalTheory.Conv.ev_congr {T T' : ℝ} {w : ℂ} (hw : T < w.im) (hw' : T' < w.im) {s : halfRing T}
    {s' : halfRing T'} (h : (s : ℂ⸨X⸩) = s') : ev T w hw s = ev T' w hw' s' := by sorry
