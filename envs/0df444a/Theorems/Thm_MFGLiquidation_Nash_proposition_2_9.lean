-- Prove2me | Theorems.Thm_MFGLiquidation_Nash_proposition_2_9
-- name    : MFGLiquidation.Nash.proposition_2_9
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T03:31:09.393327+00:00
-- url     : https://prove2.me/theorems/159e0827-8fd8-4af5-ae5c-91b00fe3f1b3
-- title:
--   Theorem 2.4(1) / Proposition 2.9: $\xi^*=Y/(2\eta)$ is optimal given any version $\mu^*$ of $\mathbb E[\xi^*_t\mid\mathcal F^0_t]$
-- statement:
--   Let $(X,Y,Z)$ be a solution of the conditional mean-field FBSDE (2.3) for the representative player's data $(T,\widetilde W,\mathcal X,\kappa,\lambda,\eta)$, in the class of Theorem 2.4:
--   $$(X,Y,Z)\in\mathcal H_\alpha\times L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R)\times L^2_{\mathbb F}([0,T-]\times\Omega;\mathbb R^m),$$
--   and assume the standing Assumption 2.3. Put $\xi^*_t=Y_t/(2\eta_t)$ (the strategy (2.2)) and let $\mu^*$ be any $\mathbb F^0$-progressive version of
--   $$\mu^*_t=\mathbb E\Big[\frac{Y_t}{2\eta_t}\,\Big|\,\mathcal F^0_t\Big].$$
--   Then $\xi^*$ is an optimal control for the representative player given $\mu^*$: $\xi^*\in\mathcal A_{\mathbb F}(\mathcal X)$ and, for every admissible $\xi\in\mathcal A_{\mathbb F}(\mathcal X)$,
--   $$J(\mathcal X,\xi^*;\mu^*)\le J(\mathcal X,\xi;\mu^*)\qquad\text{a.s.},$$
--   where $J(\mathcal X,\xi;\mu)=\mathbb E\big[\int_0^T(\kappa_sX^\xi_s\mu_s+\eta_s\xi_s^2+\lambda_s(X^\xi_s)^2)\,ds\,\big|\,\mathcal X\big]$ is the conditional cost of the representative player.
--
--   This is item 1 of Theorem 2.4 (proved in Proposition 2.9), restated over the definitions of the Nash-equilibrium chapter (Section 3) so that it applies to each player $i$ of the $N$-player game, whose data $(T,(W^0,W^i),\mathcal X^i,\kappa^i,\lambda^i,\eta^i)$ is a representative-player data set. It is the inequality "$J^1(\xi;\mu^*)\ge J^1(\xi^{*,1};\mu^*)$ by Proposition 2.9" used in the proof of Theorem 3.3 (p. 23).
--
--   **Formalization Note.** The solution is any solution in the class of Theorem 2.4 (unique by that theorem), so the statement is Theorem 2.4(1) for the solution at hand. It coincides with the optimality conjunct of `MFGLiquidation.Equilibrium.theorem_2_4`, over the chapter-3 copies of the definitions (`MFGLiquidation.Nash.*`).
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 9, Theorem 2.4 (1); p. 15, Proposition 2.9; used on p. 23 in the proof of Theorem 3.3

import Mathlib
import Definitions.Def_MFGLiquidation_Nash_Setting
import Definitions.Def_MFGLiquidation_Nash_Game

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

theorem proposition_2_9
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Data Ω k) (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (X Y : ℝ≥0 → Ω → ℝ) (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hsol : SolvesFBSDE23InClass hD X Y Z)
    (μ : ℝ≥0 → Ω → ℝ)
    (hμ : IsCondExpVersion (filtF0 hD) P D.T (fun t ω => Y t ω / (2 * D.η t ω)) μ) :
    IsOptimal hD μ (fun t ω => Y t ω / (2 * D.η t ω)) := by sorry

end MFGLiquidation.Nash
