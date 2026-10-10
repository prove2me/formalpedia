-- Prove2me | Theorems.Thm_MultiPriceOnline_Balance_theorem_5
-- name    : MultiPriceOnline.Balance.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:05.391431+00:00
-- url     : https://prove2.me/theorems/27bf2fd9-6f37-4e40-bddc-0ccc73c7b6af
-- title:
--   Theorem 5, p. 22 — Definition 3 satisfies (17)–(18) with c = (1 − e^{−α⁽¹⁾})/((1+k)(e^{1/k} − 1)), improved for m = 1
-- statement:
--   Let $k\ge1$ be an integer, $0<r^{(1)}<\dots<r^{(m)}$ a price set with $m\ge1$, and $\alpha$ its booking limits (7). Consider the randomized procedure of Definition 3 for an item with inventory $k$: one uniform seed rounds the borders $L^{(j)}$ to $\tilde L^{(j)}\in\{0,\tfrac1k,\dots,1\}$, and the value function $\tilde\Phi$ is (20). Then:
--
--   1. the procedure is a randomized procedure: every configuration it produces satisfies (14), and its value function satisfies (15);
--   2. it satisfies (17) with
--   $$
--   c=\frac{1-e^{-\alpha^{(1)}}}{(1+k)(e^{1/k}-1)};
--   $$
--   3. it satisfies (18): $\mathbb E[\tilde\Phi(\tilde L^{(j)})]\ge r^{(j)}$ for $j\in[m]$;
--   4. if $m=1$, it satisfies (17) with the improved value
--   $$
--   c=\frac{1-e^{-\alpha^{(1)}}}{(1+k)(1-e^{-1/k})}.
--   $$
--
--   With Theorem 4 this gives bounds (i) and (iii) of Theorem 1.
--
--   **Formalization Note** Part 1 makes explicit what the paper takes for granted when it calls Definition 3 a randomized procedure (p. 21: the comonotone rounding "ensures that the borders are increasing as required in (14)"). The probability of a configuration is the Lebesgue measure of the seeds in $[0,1]$ that produce it.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 22, Theorem 5; proof in App. B.1, pp. 41–43

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_Procedure

namespace MultiPriceOnline.Balance

/-- Theorem 5 (Ma–Simchi-Levi, arXiv:1905.04770v1, p. 22). For an item with inventory `k ≥ 1`, a
price set `r` with `m ≥ 1` prices and its booking limits `α`, the procedure of Definition 3 is a
randomized procedure (its configurations satisfy (14) and its value functions (15)), and it
satisfies (17)–(18) with `c = (1 − e^{−α⁽¹⁾})/((1 + k)(e^{1/k} − 1))`. If `m = 1`, it satisfies (17)
with the improved `c = (1 − e^{−α⁽¹⁾})/((1 + k)(1 − e^{−1/k}))`. -/
theorem theorem_5 (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (r α : ℕ → ℝ)
    (hr : IsPriceSet m r) (hα : IsBookingLimits m r α) :
    IsProcedure (def3Proc k m r α) ∧
    Cond17 r (def3Proc k m r α) (Fval α / ((1 + k) * (Real.exp (1 / k) - 1))) ∧
    Cond18 r (def3Proc k m r α) ∧
    (m = 1 → Cond17 r (def3Proc k m r α) (Fval α / ((1 + k) * (1 - Real.exp (-1 / k))))) := by sorry

end MultiPriceOnline.Balance
