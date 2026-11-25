-- Prove2me | Theorems.Thm_GlobalTheory_exists_mul_isIntegralElem_of_forall_discreteValuationSubring
-- name    : GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:35:33.064643+00:00
-- url     : https://prove2.me/theorems/520450e8-84b5-4214-86db-73737ed20e9f
-- title:
--   Global Theory: exists mul is Integral Elem of forall discrete Valuation Subring
-- statement:
--   The Global Theory construction uses the exists mul is Integral Elem of forall discrete Valuation Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulIsIntegralElemOfForallDiscreteValuation.lean#L7-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulIsIntegralElemOfForallDiscreteValuation.lean#L7-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulIsIntegralElemOfForallDiscreteValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring :
    ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B),
      Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) →
      ∀ (p : Ideal C), p.IsPrime → ∀ f : B,
        (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V →
          (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) →
        ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by sorry
