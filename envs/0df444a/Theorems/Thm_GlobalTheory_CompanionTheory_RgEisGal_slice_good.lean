-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_slice_good
-- name    : GlobalTheory.CompanionTheory.RgEisGal.slice_good
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:58:57.898093+00:00
-- url     : https://prove2.me/theorems/59f11a39-c130-4190-8cb4-79b95b30609e
-- title:
--   Rg Eis Gal: slice good
-- statement:
--   The Rg Eis Gal construction uses the slice good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L67-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StripEntireOfFac.lean#L67-L84

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
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem GlobalTheory.CompanionTheory.RgEisGal.slice_good {T : Type} [TopologicalSpace T] {Φ : ℂ × ℂ → T → X} (hΦ : TubeGood Φ Set.univ) :
    (∀ g, Differentiable ℂ fun y : ℂ => Φ (0, y) g) ∧
    (Continuous fun y : ℂ × T => Φ (0, y.1) y.2) ∧
    ∀ (b a : ℝ) (g : T), ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g' ∈ U,
      ‖Φ (0, z) g'‖ ≤ M := by sorry
