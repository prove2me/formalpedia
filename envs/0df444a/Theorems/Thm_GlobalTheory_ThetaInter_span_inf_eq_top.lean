-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_span_inf_eq_top
-- name    : GlobalTheory.ThetaInter.span_inf_eq_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:41.27905+00:00
-- url     : https://prove2.me/theorems/dec071c5-6a49-4946-800a-a31a378e590a
-- title:
--   Theta Inter: span inf eq top
-- statement:
--   The Theta Inter construction uses the span inf eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L361-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L361-L369

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

theorem GlobalTheory.ThetaInter.span_inf_eq_top {A₁ A₂ : AddSubgroup W} [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)]
    (hsp : Submodule.span ℝ (A₂ : Set W) = ⊤) : Submodule.span ℝ ((A₁ ⊓ A₂ : AddSubgroup W) : Set W) = ⊤ := by sorry
