-- Prove2me | Theorems.Thm_LeveragedPayouts_ShockSize_step1
-- name    : LeveragedPayouts.ShockSize.step1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:07.057891+00:00
-- url     : https://prove2.me/theorems/afa0e485-1655-4e10-8620-a460740ccaef
-- title:
--   Step 1, p. 57 — for $\rho$ close enough to 1, $(r_u,l_u)=(R,l^*)$ is the unique optimum
-- statement:
--   Fix an economy. There is $\rho_1<1$ such that for every shock $\rho$ with $\max\{\rho_1,0\}<\rho<1$:
--
--   1. the rate $r=R$, with labour $l^*$, is an optimal date-0 rate, and
--   2. every optimal date-0 rate $r_u$ with labour $l_u$ satisfies
--   $$(r_u,l_u)=(R,l^*).$$
--
--   Small shocks leave the date-0 rate at its steady-state value: this gives the threshold $\bar\rho$ of Proposition 12 its upper bound $\bar\rho<1$.
--
--   **Formalization Note** Optimality is global, against every rate $r>0$ and every feasible labour demand at $r$ (`IsOptimalRate`).
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 57, Appendix B, proof of Proposition 12, Step 1

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.ShockSize

theorem step1 (E : LeveragedPayouts.Unregulated.Economy) :
    ∃ ρ₁ < 1, ∀ ρ, 0 < ρ → ρ₁ < ρ → ρ < 1 →
      LeveragedPayouts.Unregulated.IsOptimalRate E ρ E.R E.lstar ∧
        ∀ ru lu, LeveragedPayouts.Unregulated.IsOptimalRate E ρ ru lu → ru = E.R ∧ lu = E.lstar := by sorry

end LeveragedPayouts.ShockSize
