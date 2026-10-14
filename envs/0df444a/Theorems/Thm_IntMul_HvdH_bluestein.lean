-- Prove2me | Theorems.Thm_IntMul_HvdH_bluestein
-- name    : IntMul.HvdH.bluestein
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:56:48.206329+00:00
-- url     : https://prove2.me/theorems/152d3119-910d-40ec-bbc2-d99bbc722695
-- title:
--   Bluestein's identity in $d$ dimensions: DFT $=\bar a\cdot(a*(\bar a\cdot u))$
-- statement:
--   **Bluestein's identity in $d$ dimensions.** Let $t_1,\dots,t_d$ be even positive integers and, for $j\in\prod_i\mathbb Z/t_i$, put
--   $$a_j:=\prod_{i=1}^d e^{\pi i\,\bar j_i^{\,2}/t_i},$$
--   where $\bar x\in\{0,\dots,t_i-1\}$ is the canonical representative. Because each $t_i$ is even, $e^{\pi i m^2/t_i}$ depends only on $m \bmod t_i$. Then for every $u:\prod_i\mathbb Z/t_i\to\mathbb C$ and every $j$,
--   $$\sum_k\prod_{i=1}^d e^{-2\pi i\,j_ik_i/t_i}\,u_k=\overline{a_j}\sum_k a_{j-k}\,\overline{a_k}\,u_k ,$$
--   that is, the (unnormalised) $d$-dimensional DFT equals $\bar a\cdot\big(a*(\bar a\cdot u)\big)$, with $\cdot$ the pointwise product and $*$ cyclic convolution.
--
--   This is identity (3.2) in the proof of Theorem 3.1 of Harvey–van der Hoeven. It turns the power-of-two complex DFT into a cyclic convolution, which the paper then computes with synthetic FFTs over $\mathbb C[y]/(y^r+1)$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 3.2, proof of Theorem 3.1, equations (3.1)-(3.2); Bluestein 1970

import Mathlib

namespace IntMul.HvdH
theorem bluestein {d : ℕ} (t : Fin d → ℕ) [∀ i, NeZero (t i)] (ht : ∀ i, Even (t i))
    (u : ((i : Fin d) → ZMod (t i)) → ℂ) (j : (i : Fin d) → ZMod (t i)) :
    ∑ k, (∏ i, (ZMod.stdAddChar (-(j i * k i)) : ℂ)) * u k =
      (starRingEnd ℂ) (∏ i, Complex.exp (Real.pi * Complex.I * ((j i).val : ℂ) ^ 2 / t i)) *
        ∑ k, (∏ i, Complex.exp (Real.pi * Complex.I * (((j i - k i).val : ℕ) : ℂ) ^ 2 / t i)) *
          ((starRingEnd ℂ) (∏ i, Complex.exp (Real.pi * Complex.I * ((k i).val : ℂ) ^ 2 / t i)) * u k) := by sorry
end IntMul.HvdH
