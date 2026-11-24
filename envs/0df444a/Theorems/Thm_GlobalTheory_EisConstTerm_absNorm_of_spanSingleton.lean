-- Prove2me | Theorems.Thm_GlobalTheory_EisConstTerm_absNorm_of_spanSingleton
-- name    : GlobalTheory.EisConstTerm.absNorm_of_spanSingleton
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:04.738804+00:00
-- url     : https://prove2.me/theorems/ac478c41-db5b-4add-bdbd-395ca30d0197
-- title:
--   Eis Const Term: abs Norm of span Singleton
-- statement:
--   The Eis Const Term construction uses the abs Norm of span Singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L59-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L59-L72

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

theorem GlobalTheory.EisConstTerm.absNorm_of_spanSingleton (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F) (J : Ideal (𝓞 F))
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a *
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    (Ideal.absNorm J : ℝ) = |((Algebra.norm ℚ a : ℚ) : ℝ)| * (dF F * nrm 𝔞) := by sorry
