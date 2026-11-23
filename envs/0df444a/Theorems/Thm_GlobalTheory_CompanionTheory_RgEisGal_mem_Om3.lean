-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om3
-- name    : GlobalTheory.CompanionTheory.RgEisGal.mem_Om3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:34.34884+00:00
-- url     : https://prove2.me/theorems/033e482f-03a9-445c-be0e-7780100b2930
-- title:
--   Rg Eis Gal: mem Om3
-- statement:
--   The Rg Eis Gal construction uses the mem Om3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L55-L58

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

theorem GlobalTheory.CompanionTheory.RgEisGal.mem_Om3 {N r : ℝ} {x : ℝ × ℝ} :
    x ∈ Om3 N r ↔ r < 2 * N - 1 - x.1 - 2 * x.2 ∧ r < 2 * N - 1 - x.1 := by sorry
