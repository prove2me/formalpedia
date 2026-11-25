-- Prove2me | Theorems.Thm_GlobalTheory_HCA_solG_smFn
-- name    : GlobalTheory.HCA.solG_smFn
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:29:42.562704+00:00
-- url     : https://prove2.me/theorems/a1919a1f-0367-5b2a-84f3-9bc447f2d5c8
-- title:
--   HCA: sol G sm Fn
-- statement:
--   The HCA construction uses the sol G sm Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaplacePolynomialKernelDerivativeWordsFamily.lean#L47-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LaplacePolynomialKernelDerivativeWordsFamily.lean#L47-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivWordLeIntegralOfAevalCasimirEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftTranslateSmoothCommuteLeftInvariantOpsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaplacePolynomialKernelDerivativeWordsFamily
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

theorem GlobalTheory.HCA.solG_smFn : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → (∀ f ∈ solG h b P, Continuous f) ∧ (∀ f ∈ solG h b P, ∀ g, (fun y => f (g * y)) ∈ solG h b P) ∧ ∃ K : Set G, IsCompact K ∧ ∀ l₀ : List 𝔤, SmFn h b μ (solG h b P) K fun l f => (l.map b ++ l₀).foldr h.rightDeriv f 1 := by sorry
