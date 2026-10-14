-- Prove2me | Theorems.Thm_LeveragedPayouts_ShockSize_omega_initial_segment
-- name    : LeveragedPayouts.ShockSize.omega_initial_segment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:27:57.034694+00:00
-- url     : https://prove2.me/theorems/5dd70719-8499-45d7-bd78-40313264e090
-- title:
--   Step 2, p. 58 — the set $\Omega$ of shocks with an optimum $r_u<R$ is an initial segment of $(0,1)$
-- statement:
--   Fix an economy. Let $\Omega$ be the set of shocks $\rho\in(0,1)$ for which some optimal date-0 rate $r_u$ satisfies $r_u<R$. Then $\Omega$ is closed downward in $(0,1)$: for all $0<\rho'<\rho<1$,
--   $$\rho\in\Omega\ \Longrightarrow\ \rho'\in\Omega.$$
--
--   This is the content of the paper's "$\Omega$ is an interval of the form $(0,\bar\rho)$" that Proposition 12 uses: larger shocks (smaller $\rho$) make cutting the rate weakly more attractive.
--
--   **Formalization Note** The paper defines $\Omega$ through an interior maximum over $[\underline r,R]$; here an optimum below $R$ is meant over every feasible rate $r>0$, which is the same set because no optimum lies at $\underline r$ (Step 2) or above $R$. Whether $\Omega$ is open at $\bar\rho$ is not claimed: at $\rho=\bar\rho$ an interior optimum and $r=R$ may tie.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 58, Appendix B, proof of Proposition 12, Step 2, (66)–(67)

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.ShockSize

theorem omega_initial_segment (E : LeveragedPayouts.Unregulated.Economy) :
    ∀ ρ ρ', 0 < ρ' → ρ' < ρ → ρ < 1 →
      (∃ ru lu, LeveragedPayouts.Unregulated.IsOptimalRate E ρ ru lu ∧ ru < E.R) →
        ∃ ru lu, LeveragedPayouts.Unregulated.IsOptimalRate E ρ' ru lu ∧ ru < E.R := by sorry

end LeveragedPayouts.ShockSize
