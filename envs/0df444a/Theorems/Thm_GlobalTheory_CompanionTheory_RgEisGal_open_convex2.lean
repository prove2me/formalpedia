-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_open_convex2
-- name    : GlobalTheory.CompanionTheory.RgEisGal.open_convex2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:52.400603+00:00
-- url     : https://prove2.me/theorems/de4dfcf0-e3a4-4c0b-a07d-6e2212a9a681
-- title:
--   Rg Eis Gal: open convex2
-- statement:
--   The Rg Eis Gal construction uses the open convex2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L80-L85

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

theorem GlobalTheory.CompanionTheory.RgEisGal.open_convex2 {Ω : Set (ℝ × ℝ)} (α₁ β₁ γ₁ α₂ β₂ γ₂ r : ℝ)
    (h : ∀ x, x ∈ Ω ↔ r < affR α₁ β₁ γ₁ x ∧ r < affR α₂ β₂ γ₂ x) : IsOpen Ω ∧ Convex ℝ Ω := by sorry
