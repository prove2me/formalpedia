-- Prove2me | Theorems.Thm_GlobalTheory_HCA_exists_alpha_convolution
-- name    : GlobalTheory.HCA.exists_alpha_convolution
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:29:51.437438+00:00
-- url     : https://prove2.me/theorems/9ec07ed1-7463-5536-9a33-107974330319
-- title:
--   HCA: exists alpha convolution
-- statement:
--   The HCA construction uses the exists alpha convolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothConvolutionEqDerivative.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothConvolutionEqDerivative.lean#L26-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FirstFunctionalIntegralSmoothCompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaplacePolynomialKernelDerivativeWordsFamilyStatement
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_GroundTheory_AutomorphicForms_AutomorphicFormSpaces_LeftTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothConvolutionEqDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.exists_alpha_convolution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ l : List 𝔤, ∃ α : G → ℂ, h.IsSmoothFun α ∧ Continuous α ∧ HasCompactSupport α ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g, ∫ y, (f : G → ℂ) (g * y) * α y ∂μ = l.foldr h.rightDeriv (f : G → ℂ) g := by sorry
