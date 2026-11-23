-- Prove2me | Theorems.Thm_GlobalTheory_Conv_exists_ev_ne_zero
-- name    : GlobalTheory.Conv.exists_ev_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:13.661939+00:00
-- url     : https://prove2.me/theorems/5af602bd-f78b-4a7a-be31-2c9ae4e416ac
-- title:
--   Conv: exists ev ne zero
-- statement:
--   The Conv construction uses the exists ev ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L193-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L193-L197

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

theorem GlobalTheory.Conv.exists_ev_ne_zero {T : ℝ} {s : halfRing T} (h0 : s ≠ 0) :
    ∃ T' ≥ T, ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s ≠ 0 := by sorry
