-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_setIntegral_norm_prodExp_mul_le_haar
-- name    : GlobalTheory.T.exists_setIntegral_norm_prodExp_mul_le_haar
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:43.522266+00:00
-- url     : https://prove2.me/theorems/009c17ef-cbdc-487f-9172-c51730f8aeff
-- title:
--   T: exists set Integral norm prod Exp mul le haar
-- statement:
--   The T construction uses the exists set Integral norm prod Exp mul le haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SetIntegralNormProdExpMulLeHaarStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SetIntegralNormProdExpMulLeHaarStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralNormProdExpMulLeHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralNormProdExpMulLeHaarStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_setIntegral_norm_prodExp_mul_le_haar : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ ρ > 0, ∀ K₁ : Set G, IsCompact K₁ → ∃ (C : ℝ) (K₂ : Set G), 0 ≤ C ∧ IsCompact K₂ ∧ ∀ φ : G → ℂ, Continuous φ → ∀ y ∈ K₁, ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ, ‖φ (h.prodExp b t * y)‖ ≤ C * ∫ x in K₂, ‖φ x‖ ∂μ := by sorry
