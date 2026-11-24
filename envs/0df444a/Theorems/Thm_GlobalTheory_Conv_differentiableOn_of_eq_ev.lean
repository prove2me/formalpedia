-- Prove2me | Theorems.Thm_GlobalTheory_Conv_differentiableOn_of_eq_ev
-- name    : GlobalTheory.Conv.differentiableOn_of_eq_ev
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:27:09.141814+00:00
-- url     : https://prove2.me/theorems/30747ffb-8c95-4c85-90a5-a4b07fdde60a
-- title:
--   Conv: differentiable On of eq ev
-- statement:
--   The Conv construction uses the differentiable On of eq ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L157-L159

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

theorem GlobalTheory.Conv.differentiableOn_of_eq_ev {T : ℝ} (s : halfRing T) {F : ℂ → ℂ}
    (hF : ∀ w (hw : T < w.im), F w = ev T w hw s) : DifferentiableOn ℂ F {w : ℂ | T < w.im} := by sorry
