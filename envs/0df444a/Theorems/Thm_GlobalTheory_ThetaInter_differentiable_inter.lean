-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_differentiable_inter
-- name    : GlobalTheory.ThetaInter.differentiable_inter
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:34.447673+00:00
-- url     : https://prove2.me/theorems/18bd5e9e-8765-4990-a595-58a15dfee3b1
-- title:
--   Theta Inter: differentiable inter
-- statement:
--   The Theta Inter construction uses the differentiable inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L385-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L385-L389

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

theorem GlobalTheory.ThetaInter.differentiable_inter (A₁ A₂ : AddSubgroup W) [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] {F : W → ℂ}
    (hF : Differentiable ℂ F) : Differentiable ℂ (inter H α A₁ A₂ F) := by sorry
