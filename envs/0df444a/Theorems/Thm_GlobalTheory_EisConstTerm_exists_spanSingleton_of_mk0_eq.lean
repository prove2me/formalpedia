-- Prove2me | Theorems.Thm_GlobalTheory_EisConstTerm_exists_spanSingleton_of_mk0_eq
-- name    : GlobalTheory.EisConstTerm.exists_spanSingleton_of_mk0_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:01.950854+00:00
-- url     : https://prove2.me/theorems/160883d9-4624-4c6c-a8dd-2593bd5de93f
-- title:
--   Eis Const Term: exists span Singleton of mk0 eq
-- statement:
--   The Eis Const Term construction uses the exists span Singleton of mk0 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L86-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L86-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinConstantTermPartialZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory GlobalTheory.EisConstTerm

theorem GlobalTheory.EisConstTerm.exists_spanSingleton_of_mk0_eq (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (D : (Ideal (𝓞 F))⁰)
    (J : (Ideal (𝓞 F))⁰) (hJ : ClassGroup.mk0 J = ClassGroup.mk0 D * ClassGroup.mk F 𝔞) :
    ∃ a : F, a ≠ 0 ∧ ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by sorry
