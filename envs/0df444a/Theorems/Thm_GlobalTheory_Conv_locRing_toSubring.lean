-- Prove2me | Theorems.Thm_GlobalTheory_Conv_locRing_toSubring
-- name    : GlobalTheory.Conv.locRing_toSubring
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:56.664719+00:00
-- url     : https://prove2.me/theorems/5dd8a1f2-38d3-4ed5-84d4-d754f7ea0ca1
-- title:
--   Conv: loc Ring to Subring
-- statement:
--   The Conv construction uses the loc Ring to Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L285-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L285-L294

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

theorem GlobalTheory.Conv.locRing_toSubring {T : ℝ} (s : halfRing T) :
    (locRing T s).toSubring = Subring.closure ((halfRing T : Set ℂ⸨X⸩) ∪ {(s : ℂ⸨X⸩)⁻¹}) := by sorry
