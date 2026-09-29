-- Prove2me | Theorems.Thm_Martingale_norm_prod_sub_prod_le_sum
-- name    : Martingale.norm_prod_sub_prod_le_sum
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:04:26.958569+00:00
-- url     : https://prove2.me/theorems/49c985ad-1f11-431a-9a7a-5c306fdb5ac0
-- title:
--   Telescoping estimate: $\left|\prod a_k - \prod b_k\right| \le \sum |a_k - b_k|$ for factors of modulus $\le 1$
-- statement:
--   Let $a_k, b_k$ be complex numbers of modulus at most $1$. Then for every $n$,
--
--   $$\Bigl|\prod_{k<n} a_k - \prod_{k<n} b_k\Bigr| \;\le\; \sum_{k<n} |a_k - b_k| .$$
--
--   The proof is a telescoping induction. Writing $A_m = \prod_{k<m}a_k$ and $B_m = \prod_{k<m}b_k$,
--
--   $$A_{m+1} - B_{m+1} = A_m\,(a_m - b_m) \;+\; (A_m - B_m)\,b_m ,$$
--
--   and since $|A_m| \le 1$ (a product of factors of modulus $\le 1$) and $|b_m| \le 1$, the triangle inequality bounds the left side by $|a_m - b_m| + |A_m - B_m|$, which the inductive hypothesis closes.
--
--   **Why the hypothesis is exactly modulus $\le 1$.** Without it the estimate is false — replacing one factor in a product of large numbers amplifies the perturbation by the size of the remaining factors. Boundedness by $1$ is what keeps the amplification factor at most $1$ at each step, so the errors merely add rather than compounding.
--
--   **Where it is used.** This is the aggregation step of McLeish's proof of the martingale central limit theorem. The individual comparison $|e^{i\theta z} - (1 + i\theta z)| \le \theta^2z^2$ is a statement about one factor; this lemma converts a family of such per-factor estimates into a bound on the difference of the two products, turning $\sum_k O(|\theta Z_k|^2)$ into control of $\bigl|\prod_k e^{i\theta Z_k} - \prod_k (1 + i\theta Z_k)\bigr|$. Combined with the negligibility of the increments and the boundedness of the sum of squares, that is what drives $J^{(2)}_n \Rightarrow e^{-\theta^2\sigma^2/2}$.
--
--   The statement is elementary and entirely general — no probability enters — so it is reusable wherever finite products of bounded complex numbers are compared.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2 (the telescoping estimate used in the proof).

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Finset

theorem Martingale.norm_prod_sub_prod_le_sum (a b : ℕ → ℂ) (ha : ∀ k, ‖a k‖ ≤ 1) (hb : ∀ k, ‖b k‖ ≤ 1) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, a k - ∏ k ∈ Finset.range n, b k‖
      ≤ ∑ k ∈ Finset.range n, ‖a k - b k‖ := by sorry
