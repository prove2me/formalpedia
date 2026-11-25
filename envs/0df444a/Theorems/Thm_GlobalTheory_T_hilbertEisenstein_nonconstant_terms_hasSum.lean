-- Prove2me | Theorems.Thm_GlobalTheory_T_hilbertEisenstein_nonconstant_terms_hasSum
-- name    : GlobalTheory.T.hilbertEisenstein_nonconstant_terms_hasSum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:19.148577+00:00
-- url     : https://prove2.me/theorems/cdf7ab78-00a8-5688-8b21-85546ab19b62
-- title:
--   T: hilbert Eisenstein nonconstant terms has Sum
-- statement:
--   The T construction uses the hilbert Eisenstein nonconstant terms has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinNonconstantTermsHasSumStatement.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinNonconstantTermsHasSumStatement.lean#L8-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinNonconstantTermsHasSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinNonconstantTermsHasSumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hilbertEisenstein_nonconstant_terms_hasSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
  ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k →
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z) ∧
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z c)
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z c) := by sorry
