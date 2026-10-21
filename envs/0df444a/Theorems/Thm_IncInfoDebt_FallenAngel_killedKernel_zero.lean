-- Prove2me | Theorems.Thm_IncInfoDebt_FallenAngel_killedKernel_zero
-- name    : IncInfoDebt.FallenAngel.killedKernel_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:08.714014+00:00
-- url     : https://prove2.me/theorems/d4420539-1486-46d7-8b97-fddf7e8ccad3
-- title:
--   Equation (D.22) — the killed Gaussian kernel vanishes at zero
-- statement:
--   For positive volatility $\sigma$ and positive lag $L$, with arbitrary drift $m$ and starting state $a\in\mathbb R$, the free-minus-image expression $k_L(a,y)$ in (D.2), before applying its positivity indicators, satisfies
--
--   $$k_L(a,0)=0.$$
--
--   This cancellation is the boundary value used in the Taylor expansion (D.22). It concerns the Gaussian expression itself, not the indicator that also makes the killed density zero at the boundary.
-- source:
--   Benzoni, Garlappi & Goldstein, Federal Reserve Bank of Chicago WP 2019-08 (20 Sept 2019), Online Appendix p. 18, proof of Corollary 1, (D.22), https://doi.org/10.21033/wp-2019-08

import Mathlib
import Definitions.Def_IncInfoDebt_FallenAngel_Model

namespace IncInfoDebt.FallenAngel

/-- The boundary vanishing used in (D.22), Online Appendix p. 18. -/
theorem killedKernel_zero (σ m L a : ℝ) (hP : Standing σ L) :
    killedKernel σ m L a 0 = 0 := by sorry

end IncInfoDebt.FallenAngel
