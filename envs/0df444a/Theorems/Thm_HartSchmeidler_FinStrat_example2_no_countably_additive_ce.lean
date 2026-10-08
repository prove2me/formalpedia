-- Prove2me | Theorems.Thm_HartSchmeidler_FinStrat_example2_no_countably_additive_ce
-- name    : HartSchmeidler.FinStrat.example2_no_countably_additive_ce
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:27:42.850314+00:00
-- url     : https://prove2.me/theorems/71d6a12c-bfac-4c66-9d29-a5ebf57f7544
-- title:
--   Example 2 — no countably additive correlated equilibrium
-- statement:
--   In the modified Peleg game, players are the positive integers and choose $0$ or $1$. If only finitely many players choose $1$, player $i$ receives $s^i/i^2$; otherwise the payoff is $-s^i$. There is no countably additive probability measure on the product σ-algebra satisfying the correlated-equilibrium inequalities:
--
--   $$\nexists p\text{ countably additive on }\Sigma_0\text{ such that }p\text{ satisfies (3).}$$
--
--   Example 2 establishes that the continuity assumption in Theorem 2(ii) cannot simply be removed.
--
--   **Formalization Note.** The player type is the positive naturals, so $i^2$ is never zero. Case 1 means finitely many $1$ coordinates. The impossibility on $\Sigma_0$ also rules out a countably additive equilibrium on any larger σ-algebra whose restriction to $\Sigma_0$ satisfies (3).
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 22, Example 2 ('Next, we prove ...')

import Definitions.Def_HartSchmeidler_FinStrat_Peleg

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Example 2, p. 22: the modified Peleg game has no countably additive
correlated equilibrium on the product σ-algebra. -/
theorem example2_no_countably_additive_ce :
    ¬ ∃ μ : Measure (PNat → Fin 2), IsCorrelatedEq peleg2Payoff μ := by sorry

end HartSchmeidler.FinStrat
