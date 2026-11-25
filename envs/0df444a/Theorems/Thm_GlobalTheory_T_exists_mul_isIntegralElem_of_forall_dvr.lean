-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_mul_isIntegralElem_of_forall_dvr
-- name    : GlobalTheory.T.exists_mul_isIntegralElem_of_forall_dvr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:32.702089+00:00
-- url     : https://prove2.me/theorems/cabe9668-9d5c-5b1a-a1c0-858d65941d6a
-- title:
--   T: exists mul is Integral Elem of forall dvr
-- statement:
--   The T construction uses the exists mul is Integral Elem of forall dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulIsIntegralElemOfForallDiscreteValuationStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMulIsIntegralElemOfForallDiscreteValuationStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulIsIntegralElemOfForallDiscreteValuation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulIsIntegralElemOfForallDiscreteValuationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_mul_isIntegralElem_of_forall_dvr : ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B), Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) → ∀ (p : Ideal C), p.IsPrime → ∀ f : B, (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) → ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by sorry
