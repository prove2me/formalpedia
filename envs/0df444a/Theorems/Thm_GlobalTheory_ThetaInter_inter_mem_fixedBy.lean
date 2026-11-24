-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_inter_mem_fixedBy
-- name    : GlobalTheory.ThetaInter.inter_mem_fixedBy
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:16.935638+00:00
-- url     : https://prove2.me/theorems/2c3b6483-9a79-4c2e-9f05-b55f89b2c55e
-- title:
--   Theta Inter: inter mem fixed By
-- statement:
--   The Theta Inter construction uses the inter mem fixed By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L116-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L116-L128

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

theorem GlobalTheory.ThetaInter.inter_mem_fixedBy (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)]
    (hs₁ : IsSemiChar H A₁ α) (hd₂ : IsSelfDual H A₂) (hs₂ : IsSemiChar H A₂ α)
    {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) : inter H α A₁ A₂ F ∈ fixedBy H α A₂ := by sorry
