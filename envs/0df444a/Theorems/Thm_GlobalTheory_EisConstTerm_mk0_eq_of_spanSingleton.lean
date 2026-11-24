-- Prove2me | Theorems.Thm_GlobalTheory_EisConstTerm_mk0_eq_of_spanSingleton
-- name    : GlobalTheory.EisConstTerm.mk0_eq_of_spanSingleton
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:06.879654+00:00
-- url     : https://prove2.me/theorems/839597dd-8aeb-495b-b804-954303072912
-- title:
--   Eis Const Term: mk0 eq of span Singleton
-- statement:
--   The Eis Const Term construction uses the mk0 eq of span Singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L74-L84

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

theorem GlobalTheory.EisConstTerm.mk0_eq_of_spanSingleton (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (D : (Ideal (𝓞 F))⁰) (a : F) (ha : a ≠ 0)
    (J : (Ideal (𝓞 F))⁰) (hJ : ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ClassGroup.mk0 J = ClassGroup.mk0 D * ClassGroup.mk F 𝔞 := by sorry
