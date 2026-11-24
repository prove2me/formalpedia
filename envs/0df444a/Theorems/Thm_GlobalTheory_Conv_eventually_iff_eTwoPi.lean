-- Prove2me | Theorems.Thm_GlobalTheory_Conv_eventually_iff_eTwoPi
-- name    : GlobalTheory.Conv.eventually_iff_eTwoPi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:27:20.155186+00:00
-- url     : https://prove2.me/theorems/1f4fed87-dea0-4747-a62a-b45f8afdcb23
-- title:
--   Conv: eventually iff e Two Pi
-- statement:
--   The Conv construction uses the eventually iff e Two Pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L53-L63

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

theorem GlobalTheory.Conv.eventually_iff_eTwoPi {p : ℂ → Prop} :
    (∀ᶠ v in 𝓝[≠] (0 : ℂ), p v) ↔ ∃ T : ℝ, ∀ w : ℂ, T < w.im → p (eTwoPi w) := by sorry
