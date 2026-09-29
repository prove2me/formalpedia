-- Prove2me | Theorems.Thm_OddPerfectNumber_nielsen_diophantine_bound
-- name    : OddPerfectNumber.nielsen_diophantine_bound
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-08T06:28:44.352477+00:00
-- url     : https://prove2.me/theorems/d16c0be1-af3c-4b18-8979-51138c5b4c5b
-- title:
--   Nielsen's upper bound for odd $n/d$-perfect Diophantine solutions
-- statement:
--   **Nielsen's upper bound for solutions of the perfect-number Diophantine equation.**
--
--   Fix positive integers $n$ and $d$. Following Nielsen, a positive integer $N$ is called *$n/d$-perfect* when $\sigma(N)/N = n/d$ (the fraction need not be in lowest terms); the case $n/d = 2$ is the classical notion of a perfect number. Writing $N=\prod_{i=1}^{k}p_i^{e_i}$, the equation $\sigma(N)/N = n/d$ becomes
--
--   $$
--   d\prod_{i=1}^{k}\Bigl(\sum_{j=0}^{e_i}p_i^{\,j}\Bigr)\;=\;n\prod_{i=1}^{k}p_i^{\,e_i}.
--   $$
--
--   The theorem below is the abstract form of this equation, in which the $p_i$ are replaced by arbitrary *distinct odd integers* $x_1,\dots,x_k$ greater than $1$ (they need not be prime, so the statement also covers Descartes-style "spoof" odd perfect numbers).
--
--   **Theorem.** Let $k, n, d$ be positive integers. Let $X=\{x_1,\dots,x_k\}$ be a non-empty finite set of odd integers, each greater than $1$, and let $e_1,\dots,e_k$ be positive integers such that
--
--   $$
--   d\prod_{i=1}^{k}\Bigl(\sum_{j=0}^{e_i}x_i^{\,j}\Bigr)\;=\;n\prod_{i=1}^{k}x_i^{\,e_i}.
--   $$
--
--   Then, writing $\Pi(X)=\prod_{i=1}^{k}x_i$ and $\Pi'(X)=\prod_{i=1}^{k}(x_i-1)$,
--
--   $$
--   \Bigl(\prod_{i=1}^{k}x_i^{\,e_i}\Bigr)\cdot n\,\Pi(X)\,\Pi'(X)\;<\;(d+1)^{2^{2k}} .
--   $$
--
--   Equivalently $\prod_i x_i^{e_i} < (d+1)^{4^{k}}/\bigl(n\,\Pi(X)\,\Pi'(X)\bigr)$.
--
--   This is the finiteness engine behind all known upper bounds for odd perfect numbers: for fixed $k$ it bounds every solution of the equation, and specialising to $n=2$, $d=1$ and $x_i$ the prime divisors of an odd perfect number $N$ yields the bound $N < 2^{4^{k}}$ of Nielsen (2003). The extra factor $n\,\Pi(X)\,\Pi'(X)$ on the left is the sharpening obtained in the 2015 paper, which is what makes the bound usable in computations.
--
--   **Formalization Note.** The finite set $X$ carries the distinctness of the $x_i$ automatically, $k$ is `X.card`, and the exponents are given by a function `e : ℕ → ℕ` whose values on $X$ are required to be positive. Subtraction `x - 1` is truncated subtraction on `ℕ`, which is harmless because every $x \in X$ satisfies $x > 1$.
-- source:
--   P. P. Nielsen, Odd perfect numbers, Diophantine equations, and upper bounds, Math. Comp. 84 (2015), no. 295, 2549-2567; Section 1, equation (1) and Theorem 1.6 (p. 6). Author's copy: https://mathdept.byu.edu/~pace/BestBound_web.pdf . Specialises to P. P. Nielsen, An upper bound for odd perfect numbers, INTEGERS 3 (2003), #A14, Theorem 1.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem nielsen_diophantine_bound (n d : ℕ) (X : Finset ℕ) (e : ℕ → ℕ)
    (hn : 0 < n) (hd : 0 < d) (hX : X.Nonempty)
    (hodd : ∀ x ∈ X, Odd x) (hone : ∀ x ∈ X, 1 < x) (he : ∀ x ∈ X, 0 < e x)
    (heq : d * ∏ x ∈ X, ∑ j ∈ Finset.range (e x + 1), x ^ j = n * ∏ x ∈ X, x ^ e x) :
    (∏ x ∈ X, x ^ e x) * (n * ((∏ x ∈ X, x) * ∏ x ∈ X, (x - 1)))
      < (d + 1) ^ 2 ^ (2 * X.card) := by
  sorry

end OddPerfectNumber
