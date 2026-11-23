-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_mean_eq
-- name    : GlobalTheory.ThetaInter.mean_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:57.127965+00:00
-- url     : https://prove2.me/theorems/5bf13824-ebcf-4c1c-9a90-648f0a115d60
-- title:
--   Theta Inter: mean eq
-- statement:
--   The Theta Inter construction uses the mean eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L405-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L405-L417

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

theorem GlobalTheory.ThetaInter.mean_eq {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ W) {A : AddSubgroup W}
    (hb : (Submodule.span ℤ (Set.range b)).toAddSubgroup = A) {f : W → ℝ} (hf : ∀ x ∈ A, ∀ z, f (z + x) = f z) :
    mean μ A f = ⨍ z in ZSpan.fundamentalDomain b, f z ∂μ := by sorry
