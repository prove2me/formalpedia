-- Prove2me | Theorems.Thm_GlobalTheory_Conv_evLoc_unique
-- name    : GlobalTheory.Conv.evLoc_unique
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:20.367992+00:00
-- url     : https://prove2.me/theorems/5ae990f0-c662-4476-82b8-f7e1f0312e9c
-- title:
--   Conv: ev Loc unique
-- statement:
--   The Conv construction uses the ev Loc unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L359-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L359-L367

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

theorem GlobalTheory.Conv.evLoc_unique {T : ℝ} {w : ℂ} (hw : T < w.im) {s : halfRing T}
    (hs : ev T w hw s ≠ 0) (φ : locRing T s →+* ℂ)
    (hφ : ∀ f, φ (algebraMap _ _ f) = ev T w hw f) (x : locRing T s) :
    φ x = evLoc T w hw s hs x := by sorry
