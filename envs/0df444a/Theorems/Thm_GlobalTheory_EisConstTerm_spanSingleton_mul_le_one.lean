-- Prove2me | Theorems.Thm_GlobalTheory_EisConstTerm_spanSingleton_mul_le_one
-- name    : GlobalTheory.EisConstTerm.spanSingleton_mul_le_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:03.153545+00:00
-- url     : https://prove2.me/theorems/e362403c-0068-4b18-9824-4cc45003c36e
-- title:
--   Eis Const Term: span Singleton mul le one
-- statement:
--   The Eis Const Term construction uses the span Singleton mul le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L31-L41

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

theorem GlobalTheory.EisConstTerm.spanSingleton_mul_le_one (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F) (ha : a ∈ latM 𝔞) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
      (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 := by sorry
