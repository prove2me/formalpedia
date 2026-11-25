-- Prove2me | Theorems.Thm_GlobalTheory_T_boundedDerivFunctional_contDiff_expLine
-- name    : GlobalTheory.T.boundedDerivFunctional_contDiff_expLine
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:11:00.7948+00:00
-- url     : https://prove2.me/theorems/cb97061d-d122-539a-be20-1594d8b52938
-- title:
--   T: bounded Deriv Functional cont Diff exp Line
-- statement:
--   The T construction uses the bounded Deriv Functional cont Diff exp Line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedDerivFunctionalContDiffExpLineStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedDerivFunctionalContDiffExpLineStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedDerivFunctionalContDiffExpLine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedDerivFunctionalContDiffExpLineStatement
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

theorem GlobalTheory.T.boundedDerivFunctional_contDiff_expLine : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l i, ∀ f ∈ S, ContDiff ℝ ∞ (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) ∧ ∀ (p : ℕ) (s : ℝ), iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) s = Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by sorry
