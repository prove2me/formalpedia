-- Prove2me | Theorems.Thm_HeckeTreeWalk_cast_walkCount_zero_add_sum_mul_pow_sub_pow_eq_centralBinom_mul_pow
-- name    : HeckeTreeWalk.cast_walkCount_zero_add_sum_mul_pow_sub_pow_eq_centralBinom_mul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/9cddff50-176c-5887-8e17-911df25b7c43
-- title:
--   Shell-weighted walk counts on the (q+1)-regular tree
-- statement:
--   Let $q$ be a natural number and let $W : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ be a function of two natural-number arguments subject to four hypotheses: $W(0,0) = 1$; $W(0,d+1) = 0$ for every $d$; $W(k+1,0) = (q+1)\,W(k,1)$ for every $k$; and $W(k+1,d+1) = W(k,d) + q\,W(k,d+2)$ for all $k,d$. (These conditions determine $W$ uniquely, $W(k,d)$ being the number of walks of length $k$ from the root of the $(q+1)$-regular tree to a fixed vertex at distance $d$, but the theorem assumes only the four displayed identities.) Then for every natural number $k$ the identity
--   $$W(2k,0) + \sum_{r=1}^{k} W(2k,2r)\,\bigl(q^{r} - q^{r-1}\bigr) = \binom{2k}{k} q^{k}$$
--   holds in $\mathbb{Z}$, the values of $W$ and the binomial coefficient being cast from $\mathbb{N}$ to $\mathbb{Z}$, the sum being taken over the finite interval $1 \le r \le k$, and the exponent $r-1$ being truncated natural subtraction (harmless, since $r \ge 1$ throughout the sum). No primality or positivity assumption is made on $q$.
--
--   The identity is the combinatorial core of the unipotent orbital computation for a $2k$-fold Hecke word at a place with residue field of size $q$: the walk counts $W(2k,2r)$ are the multiplicities of the double cosets at tree-distance $2r$ in the $2k$-th power of the Hecke operator, and $q^{r}-q^{r-1}$ (respectively $1$) is the mass of the corresponding shell met by the unipotent orbit; equivalently, the $2k$-th moment of the relevant measure on the tree equals $\binom{2k}{k} q^{k}$. It is used in the evaluation of twisted local zeta factors at unipotent terms, via [`TwistedUnipotentTerm.exists_forall_localZeta_twistedLocalFactor_one_one_eq_mul_centralBinom_unram`](thm.html#TwistedUnipotentTerm.exists_forall_localZeta_twistedLocalFactor_one_one_eq_mul_centralBinom_unram) and [`TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram`](thm.html#TwistedUnipotentTerm.exists_forall_deriv_localZeta_twistedLocalFactor_one_eq_weighted_moments_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeTreeWalk_cast_walkCount_zero_add_sum_mul_pow_sub_pow_eq_centralBinom_mul_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeTreeWalk.cast_walkCount_zero_add_sum_mul_pow_sub_pow_eq_centralBinom_mul_pow
    (q : ℕ) (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (q + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + q * W k (d + 2)) :
    ∀ k : ℕ, (W (2 * k) 0 : ℤ) +
        ∑ r ∈ Finset.Icc 1 k, (W (2 * k) (2 * r) : ℤ) * ((q : ℤ) ^ r - (q : ℤ) ^ (r - 1)) =
      ((2 * k).choose k : ℤ) * (q : ℤ) ^ k := by sorry
