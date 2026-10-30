-- Prove2me | Theorems.Thm_LL_Decomp1537b_nonreal_case
-- name    : LL_Decomp1537b.nonreal_case
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:33:06.628662+00:00
-- url     : https://prove2.me/theorems/548b77a2-4059-4750-a37e-8b9a774bc0b9
-- title:
--   Arithmetic step outside Iwaniec's zero free region
-- statement:
--   Let $H>0$. There is a real $Y$ such that for all reals $L_N\ge Y$, $x\ge\log2$ and $\ell$ with $1\le\ell\le2L_N$, the inequality $\dfrac{1}{4\cdot10^4\,\bigl(x+(\ell\log\ell)^{3/4}\bigr)}\le\dfrac{H}{L_N}$ implies $x\ge\dfrac{L_N}{8\cdot10^4H}$. Here $L_N$ plays the role of $\log N$ and the real power is the Mathlib real power.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem II, Acta Mathematica Hungarica, 2020; Section 2, displays (2.30) and (2.31), pp. 5 and 6

import Mathlib

open Finset Real

namespace LL_Decomp1537b
theorem nonreal_case {H : ℝ} (hH : 0 < H) :
    ∃ Y : ℝ, ∀ lN : ℝ, Y ≤ lN → ∀ x ℓ : ℝ, Real.log 2 ≤ x → 1 ≤ ℓ → ℓ ≤ 2 * lN →
      1 / (4 * 10 ^ 4 * (x + (ℓ * Real.log ℓ) ^ ((3 : ℝ) / 4))) ≤ H / lN →
      lN / (8 * 10 ^ 4 * H) ≤ x := by sorry
end LL_Decomp1537b
