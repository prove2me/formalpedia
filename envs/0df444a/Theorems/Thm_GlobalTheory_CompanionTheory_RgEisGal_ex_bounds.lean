-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_ex_bounds
-- name    : GlobalTheory.CompanionTheory.RgEisGal.ex_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:34.911493+00:00
-- url     : https://prove2.me/theorems/d8ebeaed-a0a9-4e26-8aec-97ce8f0663aa
-- title:
--   Rg Eis Gal: ex bounds
-- statement:
--   The Rg Eis Gal construction uses the ex bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L112-L115

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
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

theorem GlobalTheory.CompanionTheory.RgEisGal.ex_bounds (u R : ℝ) :
    ∃ m M : ℝ, m ≤ u ∧ m ≤ -2 * R ∧ (m = u ∨ m = -2 * R) ∧ u ≤ M ∧ R ≤ M ∧ (M = u ∨ M = R) := by sorry
