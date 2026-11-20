-- Prove2me | Theorems.Thm_LL_Decomp587f_r3Fourteen_short
-- name    : LL_Decomp587f.r3Fourteen_short
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-18T01:06:03.278136+00:00
-- url     : https://prove2.me/theorems/ed4ce3b8-7b5a-4f29-b0ea-40ed17e84b6a
-- title:
--   Bound for $I_{2,14}$ in Table 1 row four on $2\le\varphi\le13/5$
-- statement:
--   Let $\omega:\mathbb R\to\mathbb R$ be a Buchstab function in the sense above, extended by $\omega(u)=0$ for $u<1$. For every real $\varphi$ with $2\le\varphi\le13/5$, the integral of $\omega\bigl((\varphi-x_0-x_1-x_2)/x_1\bigr)/(x_0x_1x_2\cdot x_1)$ over the set $D$ of $(x_0,x_1,x_2)\in\mathbb R^3$ with $x_0\le\dots\le x_2$ and each $x_j$ between the $j$th lower and upper endpoint is at most $2640381/1000000000\approx0.0026404$. The box has lower endpoints $(25/103,100/291,100/291)$ and upper endpoints $(25/89,2/5,2/5)$, given by the definitions r3FourteenLo and r3FourteenHi. This is the Buchstab integral with $n=1$, the term $I_{2,14}$ of Table 1 row four.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, Lemma 5.2 page 26 and Table 1 row four page 30 of arXiv 0705.1652.

import Mathlib
import Definitions.Def_LL_Decomp587f_IsBuchstab
import Definitions.Def_LL_Decomp587f_ZeroBelowOne
import Definitions.Def_LL_Decomp587f_buchstabIntegral
import Definitions.Def_LL_Decomp587f_r3FourteenLo
import Definitions.Def_LL_Decomp587f_r3FourteenHi

open Real Set MeasureTheory

namespace LL_Decomp587f
theorem r3Fourteen_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (13 / 5 : ℝ)) :
    buchstabIntegral ω 1 r3FourteenLo r3FourteenHi φ ≤ (2640381 / 1000000000 : ℝ) := by sorry
end LL_Decomp587f
