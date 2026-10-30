-- Prove2me | Theorems.Thm_LL_Decomp1537b_modulus_nonreal_large
-- name    : LL_Decomp1537b.modulus_nonreal_large
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:33:30.804257+00:00
-- url     : https://prove2.me/theorems/b283d655-17db-4ded-b24e-d51e1c8db921
-- title:
--   Moduli of non real exceptional characters grow
-- statement:
--   Let $H>0$ and $T\in\mathbb R$. There is a real $Y$ such that for all reals $N\ge4$ with $\log N\ge Y$ and all reals $r',r,t,\sigma$ with $r'\ge1$, $3\le r\le N$, $|t|\le\sqrt N$, $\sigma\ge1-H/\log N$ and $\sigma\le1-\dfrac{1}{4\cdot10^4\bigl(\log(2r')+(\ell\log\ell)^{3/4}\bigr)}$, where $\ell=\log\bigl(r(|t|+2)\bigr)$, one has $\log(2r')\ge T$. The lab assembly is conditional on the open leaves nonreal_case and ell_le of this mission.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem II, Acta Mathematica Hungarica, 2020; Section 2, displays (2.30) and (2.31), pp. 5 and 6, toward (2.27) and (2.32)

import Mathlib

open Finset Real

namespace LL_Decomp1537b
theorem modulus_nonreal_large {H : ℝ} (hH : 0 < H) (T : ℝ) :
    ∃ Y : ℝ, ∀ N : ℝ, 4 ≤ N → Y ≤ Real.log N → ∀ r' r t σ : ℝ, 1 ≤ r' → 3 ≤ r → r ≤ N →
      |t| ≤ Real.sqrt N → 1 - H / Real.log N ≤ σ →
      σ ≤ 1 - 1 / (4 * 10 ^ 4 * (Real.log (2 * r') +
        (Real.log (r * (|t| + 2)) * Real.log (Real.log (r * (|t| + 2)))) ^ ((3 : ℝ) / 4))) →
      T ≤ Real.log (2 * r') := by sorry
end LL_Decomp1537b
