-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_normalized_successive_approximations
-- name    : OAI.PiExponent.exists_normalized_successive_approximations
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T11:48:08.082693+00:00
-- url     : https://prove2.me/theorems/ac557e0f-57d3-4ea8-816a-1ae5b1c6fee6
-- title:
--   Normalized successive rational approximations from a uniform power-law hypothesis
-- statement:
--   Let $\nu,X,D\in\mathbb R$ with $\nu>0$. Assume the conditional hypothesis $h_{\mathrm{bad}}$: for every $Q\in\mathbb N$ there are $p\in\mathbb Z$ and $q\in\mathbb N$ with $Q\le q$ and $$\left|\pi-\frac{p}{q}\right|\le q^{-\nu}. $$
--
--   Then there are sequences $p_n,q_n,x_n$ with $x_0=1$, $x_{n+1}=\lceil\log q_n\rceil$, the same approximation bound, $q_n\ge2$, $p_n\ne0$, $1\le\lceil\log q_n\rceil$, $X<x_{n+1}$, and
--
--   $$D\prod_{j<i}x_j<x_i\qquad(i>0).$$
--
--   This is conditional on $h_{\mathrm{bad}}$ and $\nu>0$; it does not assert that the hypothesis holds unconditionally for $\pi$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/SuccessiveApproximations.lean#L134-L147

import Lean
import Theorems.Thm_OAI_PiExponent_exists_successive_approximations
import Theorems.Thm_OAI_PiExponent_exists_normalized_selection_of_selector

theorem OAI.PiExponent.exists_normalized_successive_approximations
    (nu X D : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∃ x : ℕ → ℝ,
      x 0 = 1 ∧
      (∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)) ∧
      (∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧ X < x (n + 1)) ∧
      (∀ i, 1 ≤ x i) ∧
      (∀ i, 0 < i → D * (∏ j ∈ Finset.range i, x j) < x i) := by sorry
