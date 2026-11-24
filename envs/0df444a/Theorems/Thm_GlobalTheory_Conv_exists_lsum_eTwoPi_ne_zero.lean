-- Prove2me | Theorems.Thm_GlobalTheory_Conv_exists_lsum_eTwoPi_ne_zero
-- name    : GlobalTheory.Conv.exists_lsum_eTwoPi_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:35.219128+00:00
-- url     : https://prove2.me/theorems/425d9c00-c2e4-4fa4-9cfe-f21b017757ed
-- title:
--   Conv: exists lsum e Two Pi ne zero
-- statement:
--   The Conv construction uses the exists lsum e Two Pi ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L189-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L189-L191

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

theorem GlobalTheory.Conv.exists_lsum_eTwoPi_ne_zero {s : ℂ⸨X⸩} (hs : s ∈ convLaurent) (h0 : s ≠ 0) :
    ∃ T : ℝ, ∀ w : ℂ, T < w.im → lsum s (eTwoPi w) ≠ 0 := by sorry
