-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_chain4
-- name    : GlobalTheory.CompanionTheory.RgEisGal.chain4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:58:21.074405+00:00
-- url     : https://prove2.me/theorems/ffa1f9f3-2f42-4694-9ab1-d4baa514637c
-- title:
--   Rg Eis Gal: chain4
-- statement:
--   The Rg Eis Gal construction uses the chain4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L175-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChamberPairThreeFour.lean#L175-L191

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

theorem GlobalTheory.CompanionTheory.RgEisGal.chain4 (hTC : TubeChain) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {T : Type} [TopologicalSpace T] [FirstCountableTopology T] {Ω₀ Ω₁ Ω₂ Ω₃ : Set (ℝ × ℝ)}
    {F₀ F₁ F₂ F₃ : ℂ × ℂ → T → X}
    (h₀ : IsOpen Ω₀ ∧ Convex ℝ Ω₀ ∧ TubeGood F₀ Ω₀) (h₁ : IsOpen Ω₁ ∧ Convex ℝ Ω₁ ∧ TubeGood F₁ Ω₁)
    (h₂ : IsOpen Ω₂ ∧ Convex ℝ Ω₂ ∧ TubeGood F₂ Ω₂) (h₃ : IsOpen Ω₃ ∧ Convex ℝ Ω₃ ∧ TubeGood F₃ Ω₃)
    (j₀ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₀ ∩ Ω₁ ∧ ∀ l ∈ tube V, ∀ g, F₀ l g = F₁ l g)
    (j₁ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₁ ∩ Ω₂ ∧ ∀ l ∈ tube V, ∀ g, F₁ l g = F₂ l g)
    (j₂ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₂ ∩ Ω₃ ∧ ∀ l ∈ tube V, ∀ g, F₂ l g = F₃ l g)
    (mid : ∀ x : ℝ × ℝ, ∃ a ∈ Ω₀, ∃ b ∈ Ω₃, x = midpoint ℝ a b) :
    ∃ Φ : ℂ × ℂ → T → X, TubeGood Φ Set.univ ∧
      (∀ l ∈ tube Ω₀, ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F₀ l g) ∧
      ∀ l ∈ tube Ω₃, ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F₃ l g := by sorry
