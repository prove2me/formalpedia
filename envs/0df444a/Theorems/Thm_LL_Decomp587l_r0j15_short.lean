-- Prove2me | Theorems.Thm_LL_Decomp587l_r0j15_short
-- name    : LL_Decomp587l.r0j15_short
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-18T01:27:47.078582+00:00
-- url     : https://prove2.me/theorems/a35c9c03-acd0-4d20-88a5-aaffe41f491b
-- title:
--   Bound for $I_{2,15}$ in Table 1 row one on $2\le\varphi\le7/2$
-- statement:
--   Let $\omega:\mathbb R\to\mathbb R$ be a Buchstab function in the sense above, extended by $\omega(u)=0$ for $u<1$. For every real $\varphi$ with $2\le\varphi\le7/2$, the integral of $\omega\bigl((\varphi-x_0-x_1-x_2)/x_1\bigr)/(x_0x_1x_2\cdot x_1)$ over the set $D$ of $(x_0,x_1,x_2)\in\mathbb R^3$ with $x_0\le\dots\le x_2$ and each $x_j$ between the $j$th lower and upper endpoint is at most $662003/125000000\approx0.0052960$. The box has lower endpoints $(100/353,10/29,25/61)$ and upper endpoints $(10/29,25/61,5/11)$, given by the definitions r0j15_lo and r0j15_hi. This is the Buchstab integral with $n=1$, the term $I_{2,15}$ of Table 1 row one.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, Lemma 5.2 page 26 and Table 1 row one page 30 of arXiv 0705.1652.

import Mathlib
import Definitions.Def_LL_Decomp587l_IsBuchstab
import Definitions.Def_LL_Decomp587l_ZeroBelowOne
import Definitions.Def_LL_Decomp587l_buchstabIntegral
import Definitions.Def_LL_Decomp587l_r0j15_lo
import Definitions.Def_LL_Decomp587l_r0j15_hi

open Real Set Finset MeasureTheory

namespace LL_Decomp587l
theorem r0j15_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j15_lo j : ℝ)) (fun j => (r0j15_hi j : ℝ)) φ ≤ ((662003 / 125000000) : ℝ) := by sorry
end LL_Decomp587l
