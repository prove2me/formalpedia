-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_inter_eq
-- name    : GlobalTheory.ThetaInter.inter_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:43.473808+00:00
-- url     : https://prove2.me/theorems/00f010bd-00c6-406f-ac3b-ae554a163b23
-- title:
--   Theta Inter: inter eq
-- statement:
--   The Theta Inter construction uses the inter eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L109-L114

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

theorem GlobalTheory.ThetaInter.inter_eq (A₁ A₂ : AddSubgroup V) [Fintype (A₂ ⧸ A₁.addSubgroupOf A₂)] (F : V → ℂ) :
    inter H α A₁ A₂ F = fun z => ((Real.sqrt (Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂)) : ℝ) : ℂ)⁻¹ *
      ∑ c : A₂ ⧸ A₁.addSubgroupOf A₂,
        α ((Quotient.out c : A₂) : V) * opU H ((Quotient.out c : A₂) : V) F z := by sorry
