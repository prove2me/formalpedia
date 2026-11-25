-- Prove2me | Theorems.Thm_GlobalTheory_HCA_SmFn_exists_decomp_prodExp
-- name    : GlobalTheory.HCA.SmFn.exists_decomp_prodExp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:44:25.294151+00:00
-- url     : https://prove2.me/theorems/8807aa5e-ea17-4867-97d7-64ffbe8e0768
-- title:
--   Sm Fn: exists decomp prod Exp
-- statement:
--   The Sm Fn construction uses the exists decomp prod Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDixmierMalliavinDecompProdExp.lean#L71-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDixmierMalliavinDecompProdExp.lean#L71-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStepStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousLeftTranslateBoundedDerivFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExp
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
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.SmFn.exists_decomp_prodExp : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (j : Fin n → Fin d) (Λ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ → ∃ (N : ℕ) (Λ' : Fin N → List (Fin d) → (G → ℂ) → ℂ) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ m, SmFn h b μ S K (Λ' m) ∧ ContDiff ℝ ∞ (κ m) ∧ tsupport (κ m) ⊆ Metric.closedBall 0 ε) ∧ ∀ f ∈ S, Λ [] f = ∑ m, ∫ t, κ m t * Λ' m [] fun y => f (h.prodExp (fun k => b (j k)) t * y) := by sorry
