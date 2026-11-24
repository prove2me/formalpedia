-- Prove2me | Theorems.Thm_GlobalTheory_Conv_sumsAt_ev_of_eq
-- name    : GlobalTheory.Conv.sumsAt_ev_of_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:59.320458+00:00
-- url     : https://prove2.me/theorems/1c85d3c7-d435-419f-b0b6-ed03c4f59985
-- title:
--   Conv: sums At ev of eq
-- statement:
--   The Conv construction uses the sums At ev of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L136-L140

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

theorem GlobalTheory.Conv.sumsAt_ev_of_eq {T : ℝ} {w : ℂ} (hw : T < w.im) {p : ℂ⟦X⟧} {s : halfRing T}
    (h : (p : ℂ⸨X⸩) = s) : SumsAt p w (ev T w hw s) := by sorry
