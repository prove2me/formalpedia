-- Prove2me | Theorems.Thm_GlobalTheory_Conv_sumsAt_iff
-- name    : GlobalTheory.Conv.sumsAt_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:50.780811+00:00
-- url     : https://prove2.me/theorems/6de89778-43a9-4e5d-ac74-ae74c96e9939
-- title:
--   Conv: sums At iff
-- statement:
--   The Conv construction uses the sums At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L142-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L142-L144

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

theorem GlobalTheory.Conv.sumsAt_iff {p : ℂ⟦X⟧} {w x : ℂ} :
    SumsAt p w x ↔ HasSum (fun n : ℤ => (p : ℂ⸨X⸩).coeff n * eTwoPi w ^ n) x := by sorry
