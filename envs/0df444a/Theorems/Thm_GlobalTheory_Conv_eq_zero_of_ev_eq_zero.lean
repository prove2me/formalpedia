-- Prove2me | Theorems.Thm_GlobalTheory_Conv_eq_zero_of_ev_eq_zero
-- name    : GlobalTheory.Conv.eq_zero_of_ev_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:27:23.664752+00:00
-- url     : https://prove2.me/theorems/9f9c1b8a-5bf4-423c-a368-223e24e19442
-- title:
--   Conv: eq zero of ev eq zero
-- statement:
--   The Conv construction uses the eq zero of ev eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L199-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L199-L213

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

theorem GlobalTheory.Conv.eq_zero_of_ev_eq_zero {T : ℝ} {s : halfRing T} (T' : ℝ)
    (h : ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s = 0) : s = 0 := by sorry
