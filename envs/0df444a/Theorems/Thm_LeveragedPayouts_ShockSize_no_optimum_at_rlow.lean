-- Prove2me | Theorems.Thm_LeveragedPayouts_ShockSize_no_optimum_at_rlow
-- name    : LeveragedPayouts.ShockSize.no_optimum_at_rlow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:15.704429+00:00
-- url     : https://prove2.me/theorems/396c639f-1f76-4307-a1e9-b4d13e0b5016
-- title:
--   Step 2, p. 58 — no optimal date-0 rate employs the whole labour force ($l_u\neq 1$, i.e. $r_u\neq\underline r$)
-- statement:
--   Fix an economy and a shock $\rho\in(0,1)$. Let $\underline r$ be the rate at which the date-0 labour demand (63) equals the whole labour endowment, $l(\underline r)=1$. Then no optimal date-0 rate has labour $1$: for every rate $r_u$,
--   $$(r_u,1)\ \text{is not an optimum of } \Sigma_\rho.$$
--   Equivalently, $\underline r$ is never an optimal rate.
--
--   In the proof of Proposition 12 this rules out a corner maximum at the lower end of the feasible rates, so that an optimum is either interior or at $r=R$.
--
--   **Formalization Note** The rate $\underline r$ is not defined separately: the labour bound $l\le 1$ in `IsLaborDemand` makes the rates below $\underline r$ infeasible, and labour $1$ is exactly the rate $\underline r$.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 58, Appendix B, proof of Proposition 12, Step 2

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.ShockSize

theorem no_optimum_at_rlow (E : LeveragedPayouts.Unregulated.Economy) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ ru, ¬ LeveragedPayouts.Unregulated.IsOptimalRate E ρ ru 1 := by sorry

end LeveragedPayouts.ShockSize
