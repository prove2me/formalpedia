-- Prove2me | Theorems.Thm_GlobalTheory_coeff_aeval_one_add_X_pow_sub_one_ne_zero
-- name    : GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:09:13.864526+00:00
-- url     : https://prove2.me/theorems/181c7889-4858-4e3c-a696-3667a03427a3
-- title:
--   Global Theory: coeff aeval one add X pow sub one ne zero
-- statement:
--   The Global Theory construction uses the coeff aeval one add X pow sub one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffAevalOneAddXPowSubOneNeZero.lean#L23-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffAevalOneAddXPowSubOneNeZero.lean#L23-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoeffAevalOneAddXPowSubOneNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory

theorem GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero :
    ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by sorry
