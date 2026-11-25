-- Prove2me | Theorems.Thm_GlobalTheory_eq_mul_prod_minors
-- name    : GlobalTheory.eq_mul_prod_minors
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:07.659149+00:00
-- url     : https://prove2.me/theorems/4c3aecbb-c50e-42ad-9ba4-49e2317a8270
-- title:
--   Global Theory: eq mul prod minors
-- statement:
--   The Global Theory construction uses the eq mul prod minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L312-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L312-L374

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open UnipotentInvariant

theorem GlobalTheory.eq_mul_prod_minors {K σ : Type*} [Field K] [CharZero K] [DecidableEq σ] {p : ℕ} (z : Fin p × Fin p → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ K) (c : Fin p → ℕ)
    (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = ∑ i ∈ Finset.Ici a, c i)
    (hr : ∀ a b : Fin p, a < b → ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (hc : ∀ k l : Fin p, k < l → ∀ t : K, bind₁ (fun s => X s + ∑ a, if s = z (a, l) then C t * X (z (a, k)) else 0) P = P) :
    ∃ Q : MvPolynomial σ K, (∀ w, z w ∉ Q.vars) ∧
      P = Q * ∏ i : Fin p, (Matrix.of fun a b : Fin (i.val + 1) => (X (z (Fin.castLE i.isLt a, Fin.castLE i.isLt b)) : MvPolynomial σ K)).det ^ c i := by sorry
