-- Prove2me | Theorems.Thm_LL_Decomp587j_r1j13_short
-- name    : LL_Decomp587j.r1j13_short
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-18T01:18:43.854201+00:00
-- url     : https://prove2.me/theorems/3c7df15a-0828-4b94-a304-26d1ff353754
-- title:
--   Bound for $I_{2,13}$ in Table 1 row two on $2\le\varphi\le7/2$
-- statement:
--   Let $\omega:\mathbb R\to\mathbb R$ be a Buchstab function in the sense above, extended by $\omega(u)=0$ for $u<1$. For every real $\varphi$ with $2\le\varphi\le7/2$, the integral of $\omega\bigl((\varphi-x_0-x_1-x_2)/x_1\bigr)/(x_0x_1x_2\cdot x_1)$ over the set $D$ of $(x_0,x_1,x_2)\in\mathbb R^3$ with $x_0\le\dots\le x_2$ and each $x_j$ between the $j$th lower and upper endpoint is at most $20031169/1000000000\approx0.0200312$. The box has lower endpoints $(2/9,50/177,25/72)$ and upper endpoints $(50/177,25/72,10/23)$, given by the definitions r1j13_lo and r1j13_hi. This is the Buchstab integral with $n=1$, the term $I_{2,13}$ of Table 1 row two.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, Lemma 5.2 page 26 and Table 1 row two page 30 of arXiv 0705.1652.

import Mathlib
import Definitions.Def_LL_Decomp587j_IsBuchstab
import Definitions.Def_LL_Decomp587j_ZeroBelowOne
import Definitions.Def_LL_Decomp587j_buchstabIntegral
import Definitions.Def_LL_Decomp587j_r1j13_lo
import Definitions.Def_LL_Decomp587j_r1j13_hi

open Real Set Finset MeasureTheory

namespace LL_Decomp587j
theorem r1j13_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r1j13_lo j : ℝ)) (fun j => (r1j13_hi j : ℝ)) φ ≤ ((20031169 / 1000000000) : ℝ) := by sorry
end LL_Decomp587j
