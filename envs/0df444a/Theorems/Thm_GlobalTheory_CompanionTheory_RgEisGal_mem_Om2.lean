-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om2
-- name    : GlobalTheory.CompanionTheory.RgEisGal.mem_Om2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:58.430506+00:00
-- url     : https://prove2.me/theorems/b2a5a353-f19a-468b-a88b-a27907fa724f
-- title:
--   Rg Eis Gal: mem Om2
-- statement:
--   The Rg Eis Gal construction uses the mem Om2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L51-L53

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal

theorem GlobalTheory.CompanionTheory.RgEisGal.mem_Om2 {N r : ℝ} {x : ℝ × ℝ} : x ∈ Om2 N r ↔ r < N - x.1 - x.2 ∧ r < x.2 + 1 := by sorry
