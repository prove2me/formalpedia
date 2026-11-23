-- Prove2me | Theorems.Thm_GlobalTheory_Conv_sumsAt_ev
-- name    : GlobalTheory.Conv.sumsAt_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:30.069649+00:00
-- url     : https://prove2.me/theorems/d2bdfff8-9a8e-427a-b4f3-d1e463a52761
-- title:
--   Conv: sums At ev
-- statement:
--   The Conv construction uses the sums At ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L133-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L133-L134

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

theorem GlobalTheory.Conv.sumsAt_ev {T : ℝ} {w : ℂ} (hw : T < w.im) {p : ℂ⟦X⟧} (hp : (p : ℂ⸨X⸩) ∈ halfRing T) :
    SumsAt p w (ev T w hw ⟨p, hp⟩) := by sorry
