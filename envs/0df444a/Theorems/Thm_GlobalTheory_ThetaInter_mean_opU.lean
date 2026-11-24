-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_mean_opU
-- name    : GlobalTheory.ThetaInter.mean_opU
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:11.311244+00:00
-- url     : https://prove2.me/theorems/4b56a47c-04af-4a10-a6c8-bd086accd5d4
-- title:
--   Theta Inter: mean op U
-- statement:
--   The Theta Inter construction uses the mean op U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L419-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L419-L427

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

theorem GlobalTheory.ThetaInter.mean_opU (hH : IsHerm H) {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (hs : IsSemiChar H A α) {F : W → ℂ} (hc : Continuous F)
    (hF : F ∈ fixedBy H α A) (x : W) : mean μ A (rho H (opU H x F)) = mean μ A (rho H F) := by sorry
