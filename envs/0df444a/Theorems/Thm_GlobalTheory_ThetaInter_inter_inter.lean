-- Prove2me | Theorems.Thm_GlobalTheory_ThetaInter_inter_inter
-- name    : GlobalTheory.ThetaInter.inter_inter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:32.913613+00:00
-- url     : https://prove2.me/theorems/9197a1e4-23c8-489b-a919-e92e55bc9bec
-- title:
--   Theta Inter: inter inter
-- statement:
--   The Theta Inter construction uses the inter inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L179-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IntegralDensEqZero.lean#L179-L215

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

theorem GlobalTheory.ThetaInter.inter_inter (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} [Finite (A₁ ⧸ A₂.addSubgroupOf A₁)]
    [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] (hd₁ : IsSelfDual H A₁) (hd₂ : IsSelfDual H A₂)
    (hs₁ : IsSemiChar H A₁ α) {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) :
    inter H α A₂ A₁ (inter H α A₁ A₂ F) = F := by sorry
