-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_exists_basis
-- name    : GlobalTheory.ThetaInter.exists_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:59.616814+00:00
-- url     : https://prove2.me/theorems/62ee0eea-b809-4e8b-8094-42f6a2b8f842
-- title:
--   Theta Inter: exists basis
-- statement:
--   The Theta Inter construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L351-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L351-L359

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

theorem GlobalTheory.ThetaInter.exists_basis {A : AddSubgroup W} (hA : DiscreteTopology A) (hsp : Submodule.span ℝ (A : Set W) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ W), (Submodule.span ℤ (Set.range b)).toAddSubgroup = A := by sorry
