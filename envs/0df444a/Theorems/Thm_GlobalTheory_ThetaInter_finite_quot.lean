-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_finite_quot
-- name    : GlobalTheory.ThetaInter.finite_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:53.907365+00:00
-- url     : https://prove2.me/theorems/dbeaf69a-8d8e-4671-94c7-663fda3195a9
-- title:
--   Theta Inter: finite quot
-- statement:
--   The Theta Inter construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L219-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L219-L227

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
omit [Module ℂ V]

theorem GlobalTheory.ThetaInter.finite_quot {A₁ A₂ : AddSubgroup V} (hfg : A₂.FG) (h : ∀ x ∈ A₂, ∃ m : ℕ, 0 < m ∧ m • x ∈ A₁) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := by sorry
