-- Prove2me | Theorems.Thm_GlobalTheory_derivation_sumAlgEquiv_eq_pderiv
-- name    : GlobalTheory.derivation_sumAlgEquiv_eq_pderiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:50.790895+00:00
-- url     : https://prove2.me/theorems/734b65b0-1b79-4360-bb02-ef3700480de7
-- title:
--   Global Theory: derivation sum Alg Equiv eq pderiv
-- statement:
--   The Global Theory construction uses the derivation sum Alg Equiv eq pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGenericJacobianDataIterated.lean#L9-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGenericJacobianDataIterated.lean#L9-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataOfPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataIterated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.derivation_sumAlgEquiv_eq_pderiv {Λ : Type} [CommRing Λ] {σ τ : Type}
    (d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ))
      (MvPolynomial τ (MvPolynomial σ Λ)))
    (h1 : ∀ t x, d (Sum.inl t) x = pderiv t x)
    (h2 : ∀ s x, d (Sum.inr s) (C x) = C (pderiv s x))
    (h3 : ∀ s t, d (Sum.inr s) (X t) = 0) (u : τ ⊕ σ) (y : MvPolynomial (τ ⊕ σ) Λ) :
    d u (sumAlgEquiv Λ τ σ y) = sumAlgEquiv Λ τ σ (pderiv u y) := by sorry
