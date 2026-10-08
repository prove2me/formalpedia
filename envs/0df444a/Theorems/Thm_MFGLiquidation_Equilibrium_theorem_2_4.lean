-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_theorem_2_4
-- name    : MFGLiquidation.Equilibrium.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:53.60961+00:00
-- url     : https://prove2.me/theorems/99b4339f-58bd-4047-ac90-91f3ecaa2587
-- title:
--   Theorem 2.4 — under weak interaction the FBSDE (2.3) is uniquely solvable and yields the unique equilibrium of the liquidation MFG, with value (2.7)
-- statement:
--   Under Assumption 2.3 there is a solution
--   $$(X,Y,Z)\in\mathcal H_\alpha\times L^2_{\mathbb F}([0,T]\times\Omega;\mathbb R)\times L^2_{\mathbb F}([0,T-]\times\Omega;\mathbb R^m)$$
--   of the conditional mean-field FBSDE (2.3), and it is unique in this class ($X$ agrees a.s. at each $t\le T$, $Y$ at each $t<T$, $Z$ $dt\otimes d\mathbb P$-a.e. on each $[0,\tau]$, $\tau<T$). Moreover, with $\xi^*=Y/(2\eta)$ and for any $\mathbb F^0$-progressive version
--   $$\mu^*_t=\mathbb E\Big[\frac{Y_t}{2\eta_t}\Big|\mathcal F^0_t\Big],\qquad t\in[0,T),$$
--   1. $\xi^*$ is an optimal control for the representative player given $\mu^*$, and $X^*=X$ is the optimal state process;
--   2. $\mu^*$ solves the MFG (1.7), and every solution $\mu'$ of the MFG (1.7) equals $\mu^*$ $dt\otimes d\mathbb P$-a.e.;
--   3. the value function exists and, for the solution $A$ of the singular Riccati BSDE and $B=Y-AX$,
--   $$V(\mathcal X;\mu^*)=\frac12A_0\mathcal X^2+\frac12B_0\mathcal X+\frac12\mathbb E\Big[\int_0^T\kappa_sX^*_s\mu^*_s\,ds\ \Big|\ \mathcal X\Big].$$
--
--   This is the paper's first main result: a mean-field game of optimal liquidation with common noise, stochastic coefficients and the hard constraint $X_T=0$ has a unique equilibrium, characterized by a conditional mean-field FBSDE with singular terminal behaviour.
--
--   **Formalization Note** $B_0$ is written as $Y_0-A_0\mathcal X$, the decoupling $B=Y-AX$ at time $0$ ($X_0=\mathcal X$). The formula is stated for every solution $(A,Z^A)$ of the singular Riccati BSDE; Lemma A.1 makes $A$ unique, and also shows one exists, so this is neither weaker nor vacuous. The conditional expectation in (2.6) is fixed only up to $dt\otimes d\mathbb P$-null sets, which is all (1.7) sees, so the claims are made for every progressive version. The uniqueness class of the FBSDE is $\mathcal H_\alpha\times L^2\times L^2([0,T-])$ as printed; the uniqueness of the equilibrium is among all $\mu'\in L^2_{\mathbb F^0}$ solving (1.7). Assumption 2.3 uses essential bounds for $\kappa_{\max},\eta_\star,\lambda_\star,\|\eta\|$ (see the setting).
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 8–9, Theorem 2.4, (2.6), (2.7)

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting
import Definitions.Def_MFGLiquidation_Equilibrium_Game

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem theorem_2_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (D : Data Ω k) (hD : D.Standing P) (hA : D.Assumption23 P hD) :
    ∃ (X Y : ℝ≥0 → Ω → ℝ) (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      (SolvesFBSDE23 hD X Y Z ∧ MemH (filtF hD) P D.T (D.alpha P) X ∧
        L2F (filtF hD) P D.T Y ∧ IsL2VecMinus (filtF hD) P D.T Z) ∧
      (∀ (X' Y' : ℝ≥0 → Ω → ℝ) (Z' : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
        SolvesFBSDE23 hD X' Y' Z' → MemH (filtF hD) P D.T (D.alpha P) X' →
        L2F (filtF hD) P D.T Y' → IsL2VecMinus (filtF hD) P D.T Z' →
        (∀ t ≤ D.T, X' t =ᵐ[P] X t) ∧ (∀ t < D.T, Y' t =ᵐ[P] Y t) ∧
        ∀ τ < D.T, ∀ j, AEEqT τ P (Z' j) (Z j)) ∧
      ∀ μ : ℝ≥0 → Ω → ℝ,
        IsCondExpVersion (filtF0 hD) P D.T (fun t ω => Y t ω / (2 * D.η t ω)) μ →
        IsOptimal hD μ (fun t ω => Y t ω / (2 * D.η t ω)) ∧
        (∀ t ≤ D.T, X t =ᵐ[P] stateOf D (fun t ω => Y t ω / (2 * D.η t ω)) t) ∧
        IsMFGSolution hD μ ∧
        (∀ μ' : ℝ≥0 → Ω → ℝ, IsMFGSolution hD μ' → AEEqT D.T P μ' μ) ∧
        (∃ V : Ω → ℝ, IsValue hD μ V) ∧
        ∀ (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ), IsSingularRiccati hD A ZA →
        ∀ V : Ω → ℝ, IsValue hD μ V →
          V =ᵐ[P] fun ω => A 0 ω * D.𝒳 ω ^ 2 / 2 + (Y 0 ω - A 0 ω * D.𝒳 ω) * D.𝒳 ω / 2 +
            (P[fun ω' => ∫ s in Set.Icc (0 : ℝ) D.T,
                D.κ s.toNNReal ω' * X s.toNNReal ω' * μ s.toNNReal ω' |
              MeasurableSpace.comap D.𝒳 inferInstance]) ω / 2 := by sorry

end MFGLiquidation.Equilibrium
