-- Prove2me | Theorems.Thm_HeckeTreeWalk_two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow
-- name    : HeckeTreeWalk.two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/db8b97b9-ab61-5ba3-a865-eb0b277fcf22
-- title:
--   A weighted-moment identity for walks on the (q+1)-regular tree
-- statement:
--   Let $q$ be a natural number and let $W : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ be a doubly indexed array of natural numbers subject to four recursions: $W(0,0) = 1$; $W(0,d+1) = 0$ for every $d$; $W(k+1,0) = (q+1)\,W(k,1)$ for every $k$; and $W(k+1,d+1) = W(k,d) + q\,W(k,d+2)$ for all $k,d$. (These conditions determine $W$ uniquely, $W(k,d)$ being the number of walks of length $k$ from a root to a fixed vertex at distance $d$ in the $(q+1)$-regular tree.) The conclusion is an identity in $\mathbb{Z}$, for every natural number $k$, between $$2\Bigl[(q-1)\sum_{r=1}^{k} r\,W(2k,2r)\bigl(q^{r} - q^{r-1}\bigr) - W(2k,0)\Bigr]$$ and $$(q-1)(4q)^{k} - (q+1)\binom{2k}{k} q^{k},$$ where the sum runs over the integers $r$ with $1 \le r \le k$, the values $W(2k,2r)$ and $W(2k,0)$ are cast from $\mathbb{N}$ to $\mathbb{Z}$, and the exponent $r-1$ is truncated subtraction of naturals (harmless, since $r \ge 1$ on the range of summation).
--
--   The identity evaluates a logarithmically weighted moment of the distance distribution of a $2k$-step walk on the $(q+1)$-regular tree as a fixed linear combination of $(4q)^k$ (the total number of such walks) and the central binomial value $\binom{2k}{k} q^k$. It is the combinatorial input to the computation of the derivative at $s=1$ of the local zeta integral of a $2k$-fold Hecke word at an unramified place with residue field of size $q$, used by [`TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram`](thm.html#TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeTreeWalk_two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeTreeWalk.two_mul_sub_eq_sub_mul_pow_sub_mul_centralBinom_mul_pow
    (q : ℕ) (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (q + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + q * W k (d + 2)) :
    ∀ k : ℕ, 2 * (((q : ℤ) - 1) *
          ∑ r ∈ Finset.Icc 1 k, (r : ℤ) * (W (2 * k) (2 * r) : ℤ) * ((q : ℤ) ^ r - (q : ℤ) ^ (r - 1)) -
        (W (2 * k) 0 : ℤ)) =
      ((q : ℤ) - 1) * (4 * (q : ℤ)) ^ k - ((q : ℤ) + 1) * ((2 * k).choose k : ℤ) * (q : ℤ) ^ k := by sorry
