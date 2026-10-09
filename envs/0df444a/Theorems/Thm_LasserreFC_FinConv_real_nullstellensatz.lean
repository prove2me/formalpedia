-- Prove2me | Theorems.Thm_LasserreFC_FinConv_real_nullstellensatz
-- name    : LasserreFC.FinConv.real_nullstellensatz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:16.606989+00:00
-- url     : https://prove2.me/theorems/bb3ec7cb-d651-4011-b2c4-ee2461755422
-- title:
--   Proof of Theorem 1.1, p. 8 — Real Nullstellensatz: p ≡ 0 on V_ℝ(h) ⇒ p^{2e} + σ₂ ∈ ⟨h⟩ for some SOS σ₂
-- statement:
--   Let $h_1, \dots, h_{m_1} \in \mathbb R[x]$ and let $p \in \mathbb R[x]$ vanish identically on $V_{\mathbb R}(h)$. Then there exist $e \in \mathbb N$ and an SOS polynomial $\sigma_2 \in \Sigma\mathbb R[x]^2$ such that
--
--   $$p^{2e} + \sigma_2 \in \langle h \rangle = \langle h_1, \dots, h_{m_1}\rangle.$$
--
--   This is the Real Nullstellensatz ([2, Corollary 4.1.8]) in the form used in the proof of Theorem 1.1, applied to $\hat f = f - f_{\min} - \sigma_1$.
--
--   **Formalization Note** $\langle h\rangle$ is `Ideal.span (Set.range h)` and "vanishes identically on $V_{\mathbb R}(h)$" is membership in `vanishingIdeal ℝ V_ℝ(h)`. The page names the exponent $\ell$; it is $e$ here because $\ell$ also denotes a dimension in the paper.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 8, proof of Theorem 1.1 (Real Nullstellensatz, [2, Corollary 4.1.8])

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting

namespace LasserreFC.FinConv

open MvPolynomial

/-- Real Nullstellensatz, as used in the proof of Theorem 1.1, p. 8 ([2, Corollary 4.1.8]): a polynomial
`p` vanishing identically on `V_ℝ(h)` satisfies `p^{2e} + σ₂ ∈ ⟨h⟩` for some `e ∈ ℕ` and some sum of
squares `σ₂`. -/
theorem real_nullstellensatz {n m1 m2 : ℕ} (P : POP n m1 m2) (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ vanishingIdeal ℝ (realVariety P)) :
    ∃ e : ℕ, ∃ σ2 : MvPolynomial (Fin n) ℝ,
      IsSumSq σ2 ∧ p ^ (2 * e) + σ2 ∈ Ideal.span (Set.range P.h) := by sorry

end LasserreFC.FinConv
