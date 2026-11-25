-- Prove2me | Theorems.Thm_GlobalTheory_derivWord_le_integral_of_aeval_casimir_eq_zero
-- name    : GlobalTheory.derivWord_le_integral_of_aeval_casimir_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:49:57.023467+00:00
-- url     : https://prove2.me/theorems/99370619-cfda-5562-b3ba-d9f3d3e258a2
-- title:
--   Global Theory: deriv Word le integral of aeval casimir eq zero
-- statement:
--   The Global Theory construction uses the deriv Word le integral of aeval casimir eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivWordLeIntegralOfAevalCasimirEqZero.lean#L44-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivWordLeIntegralOfAevalCasimirEqZero.lean#L44-L131

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInteriorEstimateDerivWordPolyLaplacianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralNormProdExpMulLeHaarStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftSmoothingProdExpSmoothCommuteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExpStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivWordLeIntegralOfAevalCasimirEqZero
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
open GlobalTheory
open GlobalTheory.DerivBoundIntegral

theorem GlobalTheory.derivWord_le_integral_of_aeval_casimir_eq_zero :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ K : Set G, IsCompact K ∧ ∀ l : List 𝔤, ∃ C : ℝ, ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ‖l.foldr h.rightDeriv (f : G → ℂ) 1‖ ≤ C * ∫ x in K, ‖(f : G → ℂ) x‖ ∂μ := by sorry
