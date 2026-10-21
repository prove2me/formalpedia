-- Prove2me | Theorems.Thm_IncInfoDebt_FallenAngel_deriv_closed_form
-- name    : IncInfoDebt.FallenAngel.deriv_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:31.605147+00:00
-- url     : https://prove2.me/theorems/1210a8ff-e6e8-48b6-8da8-f27938066ec3
-- title:
--   Proof of Corollary 1 — the boundary derivative in closed form
-- statement:
--   Let $\sigma,L,a>0$, and let $m$ be any real drift. For the conditional Regime 4 density $p_4(y\mid a)$ of Lemma 1, the right derivative at zero is
--
--   $$\partial_y^+p_4(0\mid a)=\frac{2}{\sigma^2}\frac{a}{\sqrt{2\pi\sigma^2L^3}}\frac{\exp[-(a+mL)^2/(2\sigma^2L)]}{N((a+mL)/\sqrt{\sigma^2L})-e^{-2am/\sigma^2}N((-a+mL)/\sqrt{\sigma^2L})}.$$
--
--   This is the final differentiation in the Online Appendix. Together with (D.25), it yields the explicit intensity in Corollary 1.
-- source:
--   Benzoni, Garlappi & Goldstein, Federal Reserve Bank of Chicago WP 2019-08 (20 Sept 2019), Online Appendix p. 19, proof of Corollary 1, differentiation yielding (32), https://doi.org/10.21033/wp-2019-08

import Mathlib
import Definitions.Def_IncInfoDebt_FallenAngel_Model

namespace IncInfoDebt.FallenAngel

/-- The differentiation yielding (32), proof of Corollary 1, Online Appendix p. 19. -/
theorem deriv_closed_form (σ m L a : ℝ) (hP : Standing σ L) (ha : 0 < a) :
    HasDerivWithinAt (condDensity σ m L a)
      (2 / σ ^ 2 *
        (a / Real.sqrt (2 * Real.pi * σ ^ 2 * L ^ 3) *
          (Real.exp (-(1 / (2 * σ ^ 2 * L)) * (a + m * L) ^ 2) /
            (N ((a + m * L) / Real.sqrt (σ ^ 2 * L)) -
              Real.exp (-(2 * a * m / σ ^ 2)) *
                N ((-a + m * L) / Real.sqrt (σ ^ 2 * L))))))
      (Set.Ici 0) 0 := by sorry

end IncInfoDebt.FallenAngel
