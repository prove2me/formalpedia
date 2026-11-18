-- Prove2me | Theorems.Thm_LL_Decomp587h_r2j14_short
-- name    : LL_Decomp587h.r2j14_short
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-18T01:13:23.465227+00:00
-- url     : https://prove2.me/theorems/bdf23003-97b5-407d-b3a2-3d176e4ab99d
-- title:
--   Bound for $I_{2,14}$ in Table 1 row three on $2\le\varphi\le7/2$
-- statement:
--   Let $\omega:\mathbb R\to\mathbb R$ be a Buchstab function in the sense above, extended by $\omega(u)=0$ for $u<1$. For every real $\varphi$ with $2\le\varphi\le7/2$, the integral of $\omega\bigl((\varphi-x_0-x_1-x_2)/x_1\bigr)/(x_0x_1x_2\cdot x_1)$ over the set $D$ of $(x_0,x_1,x_2)\in\mathbb R^3$ with $x_0\le\dots\le x_2$ and each $x_j$ between the $j$th lower and upper endpoint is at most $54491/10000000\approx0.0054491$. The box has lower endpoints $(50/223,100/287,100/287)$ and upper endpoints $(100/357,5/12,5/12)$, given by the definitions r2j14_lo and r2j14_hi. This is the Buchstab integral with $n=1$, the term $I_{2,14}$ of Table 1 row three.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, Lemma 5.2 page 26 and Table 1 row three page 30 of arXiv 0705.1652.

import Mathlib
import Definitions.Def_LL_Decomp587h_IsBuchstab
import Definitions.Def_LL_Decomp587h_ZeroBelowOne
import Definitions.Def_LL_Decomp587h_buchstabIntegral
import Definitions.Def_LL_Decomp587h_r2j14_lo
import Definitions.Def_LL_Decomp587h_r2j14_hi

open Real Set Finset MeasureTheory

namespace LL_Decomp587h
theorem r2j14_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r2j14_lo j : ℝ)) (fun j => (r2j14_hi j : ℝ)) φ ≤ ((54491 / 10000000) : ℝ) := by sorry
end LL_Decomp587h
