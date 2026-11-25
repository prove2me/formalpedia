-- Prove2me | Theorems.Thm_GlobalTheory_T_hasSum_hilbertEisenstein_constantTerm_partialZeta
-- name    : GlobalTheory.T.hasSum_hilbertEisenstein_constantTerm_partialZeta
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:56.908297+00:00
-- url     : https://prove2.me/theorems/42155384-4555-4483-b14b-3b61109c0d0d
-- title:
--   T: has Sum hilbert Eisenstein constant Term partial Zeta
-- statement:
--   The T construction uses the has Sum hilbert Eisenstein constant Term partial Zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZetaStatement.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZetaStatement.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinConstantTermPartialZeta
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinConstantTermPartialZetaStatement
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

theorem GlobalTheory.T.hasSum_hilbertEisenstein_constantTerm_partialZeta : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (s : ℕ), 1 ≤ s →
  ∀ (D : (Ideal (NumberField.RingOfIntegers F))⁰), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) →
  ∀ Z : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) Z →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 = 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 (2 * s) 0 z c)
      (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F * GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) * Z ((2 * s : ℕ) : ℂ)) := by sorry
