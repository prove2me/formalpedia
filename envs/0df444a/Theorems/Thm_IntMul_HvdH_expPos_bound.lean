-- Prove2me | Theorems.Thm_IntMul_HvdH_expPos_bound
-- name    : IntMul.HvdH.expPos_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:22:09.599305+00:00
-- url     : https://prove2.me/theorems/f85694fa-05d5-4f40-bb69-653f82f5611b
-- title:
--   $n$-bit approximation of $2^{-\sigma}e^{\pi j/k}$ (Lemma 2.14)
-- statement:
--   Let $n,j,\sigma\ge0$ and $k\ge1$ be integers with $e^{\pi j/k}\le2^\sigma$ and $\sigma\le2n$, and let $w$ = `expPos n k j σ` (see `IntMul_HvdH_RealExp`). Then
--   $$\bigl|2^{-n}w-2^{-\sigma}e^{\pi j/k}\bigr|\le2^{-n}.$$
--   This is Lemma 2.14 of Harvey–van der Hoeven for an explicit algorithm.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemmas 2.13 and 2.14 (real exponentials)

import Definitions.Def_IntMul_HvdH_RealExp
import Theorems.Thm_IntMul_HvdH_piBits_bound
import Theorems.Thm_IntMul_HvdH_log2Bits_bound
import Theorems.Thm_IntMul_HvdH_expBits_bound

namespace IntMul.HvdH
theorem expPos_bound (n k j σ : ℕ) (hk : 0 < k) (hσ : Real.exp (Real.pi * j / k) ≤ 2 ^ σ)
    (hσn : σ ≤ 2 * n) :
    |(expPos n k j σ : ℝ) - 2 ^ n * ((2 ^ σ)⁻¹ * Real.exp (Real.pi * j / k))| ≤ 1 := by sorry
end IntMul.HvdH
