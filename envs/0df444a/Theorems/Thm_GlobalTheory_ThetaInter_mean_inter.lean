-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_mean_inter
-- name    : GlobalTheory.ThetaInter.mean_inter
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:02.552124+00:00
-- url     : https://prove2.me/theorems/6b3b9b0b-a4b7-4025-b245-14f1163633ef
-- title:
--   Theta Inter: mean inter
-- statement:
--   The Theta Inter construction uses the mean inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L446-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L446-L514

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}
open MeasureTheory
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}
variable [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]

theorem GlobalTheory.ThetaInter.mean_inter (hH : IsHerm H) {A₁ A₂ : AddSubgroup W} [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)]
    (hA₁ : DiscreteTopology A₁) (hsp₁ : Submodule.span ℝ (A₁ : Set W) = ⊤)
    (hA₂ : DiscreteTopology A₂) (hsp₂ : Submodule.span ℝ (A₂ : Set W) = ⊤)
    (hd₁ : IsSelfDual H A₁) (hs₁ : IsSemiChar H A₁ α) (hd₂ : IsSelfDual H A₂) (hs₂ : IsSemiChar H A₂ α)
    {F : W → ℂ} (hc : Differentiable ℂ F) (hF : F ∈ fixedBy H α A₁) :
    mean μ A₂ (rho H (inter H α A₁ A₂ F)) = mean μ A₁ (rho H F) := by sorry
