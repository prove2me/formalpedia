-- Prove2me | Theorems.Thm_GlobalTheory_Conv_analyticOnNhd_lsum_eTwoPi
-- name    : GlobalTheory.Conv.analyticOnNhd_lsum_eTwoPi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:25:39.945979+00:00
-- url     : https://prove2.me/theorems/f219c5eb-3c07-45cd-80b7-80ad9c767048
-- title:
--   Conv: analytic On Nhd lsum e Two Pi
-- statement:
--   The Conv construction uses the analytic On Nhd lsum e Two Pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L146-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L146-L151

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

theorem GlobalTheory.Conv.analyticOnNhd_lsum_eTwoPi {T : ℝ} {s : ℂ⸨X⸩} (hs : s ∈ halfRing T) :
    AnalyticOnNhd ℂ (fun w => lsum s (eTwoPi w)) {w : ℂ | T < w.im} := by sorry
