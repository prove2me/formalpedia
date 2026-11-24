-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PeriodisedMean_setLIntegral_tsum_comp_inv_eq
-- name    : GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:07:33.058807+00:00
-- url     : https://prove2.me/theorems/6e5ef7c7-eb88-4940-a038-8bdbec4ee575
-- title:
--   Periodised Mean: set LIntegral tsum comp inv eq
-- statement:
--   The Periodised Mean construction uses the set LIntegral tsum comp inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainFibrationVolume.lean#L9-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainFibrationVolume.lean#L9-L79

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFibrationVolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PeriodisedMean

theorem GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ : Subgroup N) [Countable Γ] (𝓕N : Set N), IsFundamentalDomain Γ 𝓕N ν → ν 𝓕N < ⊤ → ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (dA : Measure V) [dA.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (D : Set V), IsAddFundamentalDomain Λ D dA → dA D = 1 → ∀ l : N → V, Continuous l → (∀ x y, l (x * y) = l x + l y) → Function.Surjective l → (∀ γ ∈ Γ, l γ ∈ Λ) → ∀ f : V → ℝ≥0∞, Measurable f → ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν = ν 𝓕N * ∫⁻ x, f x ∂dA := by sorry
