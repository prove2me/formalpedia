-- Prove2me | Theorems.Thm_GlobalTheory_T_fundamental_domain_fibration_volume
-- name    : GlobalTheory.T.fundamental_domain_fibration_volume
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:36.194297+00:00
-- url     : https://prove2.me/theorems/75f7ac73-4a7f-4849-879d-1aa93191947b
-- title:
--   T: fundamental domain fibration volume
-- statement:
--   The T construction uses the fundamental domain fibration volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainFibrationVolumeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainFibrationVolumeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFibrationVolume
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFibrationVolumeStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fundamental_domain_fibration_volume : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ : Subgroup N) [Countable Γ] (𝓕N : Set N), IsFundamentalDomain Γ 𝓕N ν → ν 𝓕N < ⊤ → ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (dA : Measure V) [dA.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (D : Set V), IsAddFundamentalDomain Λ D dA → dA D = 1 → ∀ l : N → V, Continuous l → (∀ x y, l (x * y) = l x + l y) → Function.Surjective l → (∀ γ ∈ Γ, l γ ∈ Λ) → ∀ f : V → ℝ≥0∞, Measurable f → ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν = ν 𝓕N * ∫⁻ x, f x ∂dA := by sorry
