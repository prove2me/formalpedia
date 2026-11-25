-- Prove2me | Theorems.Thm_GlobalTheory_T_dixmierMalliavin_factorisation_basis_step
-- name    : GlobalTheory.T.dixmierMalliavin_factorisation_basis_step
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:10:46.116137+00:00
-- url     : https://prove2.me/theorems/8a0c58ea-f2bc-5ef1-8128-a6cadc9c6a09
-- title:
--   T: dixmier Malliavin factorisation basis step
-- statement:
--   The T construction uses the dixmier Malliavin factorisation basis step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DixmierMalliavinFactorisationBasisStepStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DixmierMalliavinFactorisationBasisStepStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStepStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.dixmierMalliavin_factorisation_basis_step : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ (i : Fin d) (ε : ℝ), 0 < ε → ∃ (Λ' : List (Fin d) → (G → ℂ) → ℂ) (u v : ℝ → ℂ), SmFn h b μ S K Λ' ∧ ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ v ∧ tsupport u ⊆ Set.Icc (-ε) ε ∧ tsupport v ⊆ Set.Icc (-ε) ε ∧ ∀ f ∈ S, Λ [] f = (∫ t, u t * Λ' [] fun y => f (h.expG (t • b i) * y)) + ∫ t, v t * Λ [] fun y => f (h.expG (t • b i) * y) := by sorry
