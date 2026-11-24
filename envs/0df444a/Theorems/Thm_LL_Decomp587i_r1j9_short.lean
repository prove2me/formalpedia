-- Prove2me | Theorems.Thm_LL_Decomp587i_r1j9_short
-- name    : LL_Decomp587i.r1j9_short
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-20T07:40:32.1816+00:00
-- url     : https://prove2.me/theorems/b1e62744-63d8-4f3f-b63d-ddd18faec81c
-- title:
--   Bound for $I_{2,9}$ in Table 1 row two on $2\le\varphi\le7/2$
-- statement:
--   Let $\omega:\mathbb R\to\mathbb R$ be a Buchstab function in the sense above, extended by $\omega(u)=0$ for $u<1$. For every real $\varphi$ with $2\le\varphi\le7/2$, the integral of $\omega\bigl((\varphi-x_0-x_1-x_2)/x_1\bigr)/(x_0x_1x_2\cdot x_1)$ over the set $D$ of $(x_0,\dots,x_2)\in\mathbb R^3$ with $x_0\le\dots\le x_2$ and each $x_j$ between the $j$th lower and upper endpoint is at most $14713151/1000000000\approx0.0147132$. The box has lower endpoints $(50/177,50/177,50/177)$ and upper endpoints $(100/243,100/243,100/243)$, given by the definitions r1j9_lo and r1j9_hi. This is the Buchstab integral with $n=1$, the term $I_{2,9}$ of Table 1 row two.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, Lemma 5.2 page 26 and Table 1 page 30 of arXiv 0705.1652.

import Mathlib
import Definitions.Def_LL_Decomp587i_domain
import Definitions.Def_LL_Decomp587i_buchstabIntegral
import Definitions.Def_LL_Decomp587i_IsBuchstab
import Definitions.Def_LL_Decomp587i_ZeroBelowOne
import Definitions.Def_LL_Decomp587i_r1j9_lo
import Definitions.Def_LL_Decomp587i_r1j9_hi

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

namespace LL_Decomp587i
theorem r1j9_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r1j9_lo j : ℝ)) (fun j => (r1j9_hi j : ℝ)) φ ≤ ((14713151 / 1000000000) : ℝ) := by sorry
end LL_Decomp587i
