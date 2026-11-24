-- Prove2me | Theorems.Thm_LL_Decomp587k_r0j9_short
-- name    : LL_Decomp587k.r0j9_short
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-20T07:46:26.721925+00:00
-- url     : https://prove2.me/theorems/4f07925f-b61e-4e94-a8f8-22e9dca2ff78
-- title:
--   Bound for $I_{2,9}$ in Table 1 row one on $2\le\varphi\le7/2$
-- statement:
--   Let $\omega:\mathbb R\to\mathbb R$ be a Buchstab function in the sense above, extended by $\omega(u)=0$ for $u<1$. For every real $\varphi$ with $2\le\varphi\le7/2$, the integral of $\omega\bigl((\varphi-x_0-x_1-x_2)/x_1\bigr)/(x_0x_1x_2\cdot x_1)$ over the set $D$ of $(x_0,\dots,x_2)\in\mathbb R^3$ with $x_0\le\dots\le x_2$ and each $x_j$ between the $j$th lower and upper endpoint is at most $870161/62500000\approx0.0139226$. The box has lower endpoints $(100/353,100/353,100/353)$ and upper endpoints $(25/61,25/61,25/61)$, given by the definitions r0j9_lo and r0j9_hi. This is the Buchstab integral with $n=1$, the term $I_{2,9}$ of Table 1 row one.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, Lemma 5.2 page 26 and Table 1 page 30 of arXiv 0705.1652.

import Mathlib
import Definitions.Def_LL_Decomp587k_domain
import Definitions.Def_LL_Decomp587k_buchstabIntegral
import Definitions.Def_LL_Decomp587k_IsBuchstab
import Definitions.Def_LL_Decomp587k_ZeroBelowOne
import Definitions.Def_LL_Decomp587k_r0j9_lo
import Definitions.Def_LL_Decomp587k_r0j9_hi

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Real Set Finset MeasureTheory

namespace LL_Decomp587k
theorem r0j9_short {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (7 / 2 : ℝ)) :
    buchstabIntegral ω 1 (fun j => (r0j9_lo j : ℝ)) (fun j => (r0j9_hi j : ℝ)) φ ≤ ((870161 / 62500000) : ℝ) := by sorry
end LL_Decomp587k
