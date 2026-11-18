-- Prove2me | Theorems.Thm_LL_Decomp587g_r0j18_short
-- name    : LL_Decomp587g.r0j18_short
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-18T00:59:03.546534+00:00
-- url     : https://prove2.me/theorems/817f6600-521b-4569-99ca-1ba1ac2ac52b
-- title:
--   Bound for $I_{2,18}$ in Table 1 row one on $2\le\varphi\le7/2$
-- statement:
--   Let $\omega:\mathbb R\to\mathbb R$ be a Buchstab function in the sense above, extended by $\omega(u)=0$ for $u<1$. For every real $\varphi$ with $2\le\varphi\le7/2$, the integral of $\omega\bigl((\varphi-x_0-x_1-x_2-x_3)/x_2\bigr)/(x_0x_1x_2x_3\cdot x_2)$ over the set $D$ of $(x_0,x_1,x_2,x_3)\in\mathbb R^4$ with $x_0\le\dots\le x_3$ and each $x_j$ between the $j$th lower and upper endpoint is at most $155569/1000000000\approx0.0001556$. The box has lower endpoints $(10/29,10/29,25/61,25/61)$ and upper endpoints $(25/61,25/61,5/11,5/11)$, given by the definitions r0j18_lo and r0j18_hi. This is the Buchstab integral with $n=2$, the term $I_{2,18}$ of Table 1 row one.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, Lemma 5.2 page 26 and Table 1 row one page 30 of arXiv 0705.1652.

import Mathlib
import Definitions.Def_LL_Decomp587g_IsBuchstab
import Definitions.Def_LL_Decomp587g_ZeroBelowOne
import Definitions.Def_LL_Decomp587g_buchstabIntegral
import Definitions.Def_LL_Decomp587g_r0j18_lo
import Definitions.Def_LL_Decomp587g_r0j18_hi

open Real Set Finset MeasureTheory

namespace LL_Decomp587g
theorem r0j18_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 2 (fun j => (r0j18_lo j : ℝ)) (fun j => (r0j18_hi j : ℝ)) φ ≤ ((155569 / 1000000000) : ℝ) := by sorry
end LL_Decomp587g
