-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om4
-- name    : GlobalTheory.CompanionTheory.RgEisGal.mem_Om4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:37.86858+00:00
-- url     : https://prove2.me/theorems/0a505d0a-5833-4d29-88ec-94281f023f22
-- title:
--   Rg Eis Gal: mem Om4
-- statement:
--   The Rg Eis Gal construction uses the mem Om4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L60-L63

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

theorem GlobalTheory.CompanionTheory.RgEisGal.mem_Om4 {N r : ℝ} {x : ℝ × ℝ} :
    x ∈ Om4 N r ↔ (r < N - 1 - x.2 ∧ r < 2 * N - 1 - x.2 - x.1) ∧ x.1 < 1 / 2 := by sorry
