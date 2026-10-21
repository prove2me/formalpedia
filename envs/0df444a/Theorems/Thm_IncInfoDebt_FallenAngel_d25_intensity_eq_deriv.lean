-- Prove2me | Theorems.Thm_IncInfoDebt_FallenAngel_d25_intensity_eq_deriv
-- name    : IncInfoDebt.FallenAngel.d25_intensity_eq_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:32.322863+00:00
-- url     : https://prove2.me/theorems/4558b3be-15ba-4d8b-9efc-5220083ff134
-- title:
--   Equation (D.25) — default intensity equals the boundary density flux
-- statement:
--   Assume $\sigma>0$, $L>0$, arbitrary drift $m$, and lagged log distance $a>0$. The conditional Regime 4 density $p_4(y\mid a)$ has a right derivative $D$ at $y=0$, and the hazard quotient $H_h(a)$ of (D.19) has a positive-side limit satisfying
--
--   $$\lim_{h\downarrow0}H_h(a)=\frac{\sigma^2}{2}D,\qquad D=\partial_y^+p_4(0\mid a).$$
--
--   This identifies the paper's short-horizon default intensity with the flux of the conditional density at the absorbing boundary, as in (D.25).
--
--   **Formalization Note** Both existence of the right derivative and existence of the hazard limit are conclusions; neither is assumed.
-- source:
--   Benzoni, Garlappi & Goldstein, Federal Reserve Bank of Chicago WP 2019-08 (20 Sept 2019), Online Appendix p. 18, proof of Corollary 1, (D.25), https://doi.org/10.21033/wp-2019-08

import Mathlib
import Definitions.Def_IncInfoDebt_FallenAngel_Model

namespace IncInfoDebt.FallenAngel
open Filter

/-- Equation (D.25), Online Appendix p. 18: the hazard limit equals the boundary flux. -/
theorem d25_intensity_eq_deriv (σ m L a : ℝ)
    (hP : Standing σ L) (ha : 0 < a) :
    ∃ D : ℝ, HasDerivWithinAt (condDensity σ m L a) D (Set.Ici 0) 0 ∧
      Tendsto (hazardQuotient σ m L a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (σ ^ 2 / 2 * D)) := by sorry

end IncInfoDebt.FallenAngel
