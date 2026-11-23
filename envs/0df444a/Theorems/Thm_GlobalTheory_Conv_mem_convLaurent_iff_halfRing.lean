-- Prove2me | Theorems.Thm_GlobalTheory_Conv_mem_convLaurent_iff_halfRing
-- name    : GlobalTheory.Conv.mem_convLaurent_iff_halfRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:21.310903+00:00
-- url     : https://prove2.me/theorems/3cde03c3-d062-4b78-9a57-8bf38c4f53ee
-- title:
--   Conv: mem conv Laurent iff half Ring
-- statement:
--   The Conv construction uses the mem conv Laurent iff half Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L165-L172

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

theorem GlobalTheory.Conv.mem_convLaurent_iff_halfRing {s : ℂ⸨X⸩} : s ∈ convLaurent ↔ ∃ T, s ∈ halfRing T := by sorry
