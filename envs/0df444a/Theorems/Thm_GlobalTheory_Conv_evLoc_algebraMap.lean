-- Prove2me | Theorems.Thm_GlobalTheory_Conv_evLoc_algebraMap
-- name    : GlobalTheory.Conv.evLoc_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:42.086156+00:00
-- url     : https://prove2.me/theorems/23c0bf98-45a7-47ad-bf07-bf7b80a0adf9
-- title:
--   Conv: ev Loc algebra Map
-- statement:
--   The Conv construction uses the ev Loc algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L354-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L354-L357

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

theorem GlobalTheory.Conv.evLoc_algebraMap {T : ℝ} {w : ℂ} (hw : T < w.im) {s : halfRing T}
    (hs : ev T w hw s ≠ 0) (f : halfRing T) :
    evLoc T w hw s hs (algebraMap _ _ f) = ev T w hw f := by sorry
