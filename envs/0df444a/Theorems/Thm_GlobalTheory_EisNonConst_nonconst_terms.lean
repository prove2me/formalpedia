-- Prove2me | Theorems.Thm_GlobalTheory_EisNonConst_nonconst_terms
-- name    : GlobalTheory.EisNonConst.nonconst_terms
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:52.167933+00:00
-- url     : https://prove2.me/theorems/3a0370c1-7073-4c6e-818b-9d6cf448d07b
-- title:
--   Eis Non Const: nonconst terms
-- statement:
--   The Eis Non Const construction uses the nonconst terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinNonconstantTermsHasSum.lean#L27-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinNonconstantTermsHasSum.lean#L27-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivLatticeClassesFibreSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivFourierClassesPosConeSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeSumEqConeSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinNonconstantTermsHasSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.EisNonConst
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre

theorem GlobalTheory.EisNonConst.nonconst_terms : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
  ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k →
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z) ∧
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 ≠ 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z c)
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z c) := by sorry
