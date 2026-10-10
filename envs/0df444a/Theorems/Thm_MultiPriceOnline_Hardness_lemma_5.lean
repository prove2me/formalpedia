-- Prove2me | Theorems.Thm_MultiPriceOnline_Hardness_lemma_5
-- name    : MultiPriceOnline.Hardness.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:55.357403+00:00
-- url     : https://prove2.me/theorems/dfa012a6-1cad-4908-a0cd-d21c7b0da406
-- title:
--   Lemma 5, p. 24 — the maximum of (27) is (28) (with the hypothesis that makes it true)
-- statement:
--   Let $m \ge 1$, let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set with booking limits $\alpha^{(1)}, \dots, \alpha^{(m)}$, and let $B_1 = 1, B_2, \dots, B_m$ be the solution of (24) (Proposition 4). Let $n, k \ge 1$, $j \in \{1, \dots, m\}$, $\tau \in [0,1]$, and $A_j = \sum_{\ell=j}^m \alpha^{(\ell)}$. Suppose
--
--   $$\frac{A_j - \tau}{m - j + 1} \le \alpha^{(\ell)} \qquad \text{for all } \ell = j, \dots, m.$$
--
--   Then the maximum of
--
--   $$\sum_{\ell=j}^m r^{(\ell)} B_\ell n (1 - e^{-\lambda_\ell}) k \qquad (27)$$
--
--   over $\lambda_j, \dots, \lambda_m \ge 0$ with $\sum_{\ell=j}^m \lambda_\ell \le \tau$ is attained and equals
--
--   $$nk \sum_{\ell=j}^m r^{(\ell)} B_\ell \Big(1 - \exp\Big(-\alpha^{(\ell)} + \frac{A_j - \tau}{m - j + 1}\Big)\Big). \qquad (28)$$
--
--   With $j = 1$ and $\tau = 1$, Lemma 5 evaluates the upper bound of Lemma 4.
--
--   **Formalization Note** The displayed hypothesis is not in the paper, and it is necessary. Without it the lemma is false. For $m = 2$, $j = 1$, $\tau = 0$ the constraint forces $\lambda = 0$, so the maximum is $0$. By (24), however, (28) equals $nk\, r^{(1)} (1 - e^{-a})^2$ with $a = \alpha^{(1)} - 1/2 \ne 0$. The hypothesis says that every candidate maximizer $\lambda_\ell = \alpha^{(\ell)} - (A_j - \tau)/(m-j+1)$ is nonnegative. The paper's only use, $j = 1$ and $\tau = 1$, satisfies it, since $(A_1 - 1)/m = 0$. The maximum is stated as `IsGreatest`: the value is attained and is an upper bound.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 24, Lemma 5, eqs. (27)–(28); proof p. 48, App. D

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet

namespace MultiPriceOnline.Hardness
open Finset
theorem lemma_5 {m : ℕ} {r α B : ℕ → ℝ} (hm : 1 ≤ m) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (hB : IsPhaseB m r α B) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hrep : ∀ l : ℕ, j ≤ l → l ≤ m → (Asum m α j - τ) / ((m : ℝ) - j + 1) ≤ α l) :
    IsGreatest
      {v : ℝ | ∃ lam : ℕ → ℝ, (∀ l ∈ Icc j m, 0 ≤ lam l) ∧ (∑ l ∈ Icc j m, lam l) ≤ τ ∧
        v = ∑ l ∈ Icc j m, r l * B l * n * (1 - Real.exp (-lam l)) * k}
      ((n : ℝ) * k * ∑ l ∈ Icc j m,
        r l * B l * (1 - Real.exp (-α l + (Asum m α j - τ) / ((m : ℝ) - j + 1)))) := by sorry
end MultiPriceOnline.Hardness
