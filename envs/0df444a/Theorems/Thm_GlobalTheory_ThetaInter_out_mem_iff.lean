-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_out_mem_iff
-- name    : GlobalTheory.ThetaInter.out_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:34.723287+00:00
-- url     : https://prove2.me/theorems/107f9b86-e5a3-4f7b-bfb5-b19e9e12464b
-- title:
--   Theta Inter: out mem iff
-- statement:
--   The Theta Inter construction uses the out mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L150-L152

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

theorem GlobalTheory.ThetaInter.out_mem_iff {A₁ A₂ : AddSubgroup V} (c : A₂ ⧸ A₁.addSubgroupOf A₂) :
    ((Quotient.out c : A₂) : V) ∈ A₁ ↔ c = 0 := by sorry
