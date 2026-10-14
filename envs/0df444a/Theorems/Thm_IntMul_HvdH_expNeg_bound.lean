-- Prove2me | Theorems.Thm_IntMul_HvdH_expNeg_bound
-- name    : IntMul.HvdH.expNeg_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:24:59.035895+00:00
-- url     : https://prove2.me/theorems/4d5c5878-b61c-420a-9b93-e706f30830d8
-- title:
--   $n$-bit approximation of $e^{-\pi j/k}$ (Lemma 2.13)
-- statement:
--   Let $n,j\ge0$ and $k\ge1$ be integers and let $w$ = `expNeg n k j` (see `IntMul_HvdH_RealExp`). Then
--   $$\bigl|2^{-n}w-e^{-\pi j/k}\bigr|\le2^{-n}.$$
--   This is Lemma 2.13 of Harvey–van der Hoeven for an explicit algorithm; these exponentials are the entries of the Gaussian resampling maps.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemmas 2.13 and 2.14 (real exponentials)

import Definitions.Def_IntMul_HvdH_RealExp
import Theorems.Thm_IntMul_HvdH_piBits_bound
import Theorems.Thm_IntMul_HvdH_log2Bits_bound
import Theorems.Thm_IntMul_HvdH_expBits_bound

namespace IntMul.HvdH
theorem expNeg_bound (n k j : ℕ) (hk : 0 < k) :
    |(expNeg n k j : ℝ) - 2 ^ n * Real.exp (-(Real.pi * j / k))| ≤ 1 := by sorry
end IntMul.HvdH
