-- Prove2me | Theorems.Thm_GlobalTheory_T_laplacePolynomialKernel_derivativeWords_family
-- name    : GlobalTheory.T.laplacePolynomialKernel_derivativeWords_family
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:47:57.379282+00:00
-- url     : https://prove2.me/theorems/479c0ece-a2d7-4dc3-ba26-db663827be46
-- title:
--   T: laplace Polynomial Kernel derivative Words family
-- statement:
--   The T construction uses the laplace Polynomial Kernel derivative Words family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaplacePolynomialKernelDerivativeWordsFamilyStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaplacePolynomialKernelDerivativeWordsFamilyStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaplacePolynomialKernelDerivativeWordsFamily
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaplacePolynomialKernelDerivativeWordsFamilyStatement
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

theorem GlobalTheory.T.laplacePolynomialKernel_derivativeWords_family : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → (∀ f ∈ solG h b P, Continuous f) ∧ (∀ f ∈ solG h b P, ∀ g, (fun y => f (g * y)) ∈ solG h b P) ∧ ∃ K : Set G, IsCompact K ∧ ∀ l₀ : List 𝔤, SmFn h b μ (solG h b P) K fun l f => (l.map b ++ l₀).foldr h.rightDeriv f 1 := by sorry
