-- Prove2me | Theorems.Thm_LL_Decomp587f_r3Eleven_short
-- name    : LL_Decomp587f.r3Eleven_short
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-18T01:04:48.583694+00:00
-- url     : https://prove2.me/theorems/046f5cc2-0771-4866-838b-8a90b40e4185
-- title:
--   Bound for $I_{2,11}$ in Table 1 row four on $2\le\varphi\le13/5$
-- statement:
--   Let $\omega:\mathbb R\to\mathbb R$ be a Buchstab function in the sense above, extended by $\omega(u)=0$ for $u<1$. For every real $\varphi$ with $2\le\varphi\le13/5$, the integral of $\omega\bigl((\varphi-x_0-x_1-x_2)/x_1\bigr)/(x_0x_1x_2\cdot x_1)$ over the set $D$ of $(x_0,x_1,x_2)\in\mathbb R^3$ with $x_0\le\dots\le x_2$ and each $x_j$ between the $j$th lower and upper endpoint is at most $1821597/500000000\approx0.0036432$. The box has lower endpoints $(25/89,100/291,100/291)$ and upper endpoints $(100/291,2/5,2/5)$, given by the definitions r3ElevenLo and r3ElevenHi. This is the Buchstab integral with $n=1$, the term $I_{2,11}$ of Table 1 row four.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, Lemma 5.2 page 26 and Table 1 row four page 30 of arXiv 0705.1652.

import Mathlib
import Definitions.Def_LL_Decomp587f_IsBuchstab
import Definitions.Def_LL_Decomp587f_ZeroBelowOne
import Definitions.Def_LL_Decomp587f_buchstabIntegral
import Definitions.Def_LL_Decomp587f_r3ElevenLo
import Definitions.Def_LL_Decomp587f_r3ElevenHi

open Real Set MeasureTheory

namespace LL_Decomp587f
theorem r3Eleven_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (13 / 5 : ℝ)) :
    buchstabIntegral ω 1 r3ElevenLo r3ElevenHi φ ≤ (1821597 / 500000000 : ℝ) := by sorry
end LL_Decomp587f
