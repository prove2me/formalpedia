-- Prove2me | Theorems.Thm_GlobalTheory_EisConstTerm_mem_latM_of_le_one
-- name    : GlobalTheory.EisConstTerm.mem_latM_of_le_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:52.459167+00:00
-- url     : https://prove2.me/theorems/c7b9e8eb-43eb-4422-8be0-9c1093fb7815
-- title:
--   Eis Const Term: mem lat M of le one
-- statement:
--   The Eis Const Term construction uses the mem lat M of le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L43-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L43-L57

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

theorem GlobalTheory.EisConstTerm.mem_latM_of_le_one (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F)
    (ha : FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
      (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≤ 1) : a ∈ latM 𝔞 := by sorry
