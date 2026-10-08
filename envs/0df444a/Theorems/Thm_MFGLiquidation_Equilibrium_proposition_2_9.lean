-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_proposition_2_9
-- name    : MFGLiquidation.Equilibrium.proposition_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:35.245072+00:00
-- url     : https://prove2.me/theorems/5d1a2ba7-9bc2-4ac2-a75d-66bca4029a22
-- title:
--   Proposition 2.9 — ξ* = Y/(2η) is optimal, X* = X, µ* = 𝔼[ξ*|𝓕⁰] solves the MFG (1.7), and the value is (2.7)
-- statement:
--   Assume Assumption 2.3, let $(A,Z^A)$ solve the singular Riccati BSDE, $0<\gamma<\alpha\wedge\frac12$, and let $(X,B,Y,Z^B,Z^Y)$ be a solution of (2.3) and (2.10) in the class of Proposition 2.8. Put $\xi^*_t=Y_t/(2\eta_t)$ (the strategy (2.14), equivalently (2.2)), and let $\mu^*$ be any $\mathbb F^0$-progressive version of $\mathbb E[\xi^*_t\mid\mathcal F^0_t]$. Then
--
--   1. $\xi^*$ is an optimal control for the representative player given $\mu^*$;
--   2. $X$ is the related state process: $X_t=X^{\xi^*}_t$ a.s. for each $t\le T$;
--   3. $\mu^*$ solves the MFG (1.7);
--   4. the value function given $\mu^*$ exists and equals
--   $$V(\mathcal X;\mu^*)=\frac12A_0\mathcal X^2+\frac12B_0\mathcal X+\frac12\mathbb E\Big[\int_0^T\kappa_sX^*_s\mu^*_sds\ \Big|\ \mathcal X\Big].$$
--
--   Together with Proposition 2.8 this yields the existence part of Theorem 2.4.
--
--   **Formalization Note** $X^*=X$, so the integrand of (2.7) uses $X$. The value is the essential infimum of the conditional costs. The statement says "the solution" and is stated as printed (existence of the equilibrium); uniqueness of the equilibrium, shown in its proof, is part of the goal theorem. A version $\mu^*$ exists because the solution of (2.3) carries one. Assumption 2.3 is the standing assumption of §§2–4.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 15, Proposition 2.9, (2.14); p. 9, (2.7)

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting
import Definitions.Def_MFGLiquidation_Equilibrium_Decoupled
import Definitions.Def_MFGLiquidation_Equilibrium_Game

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem proposition_2_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (D : Data Ω k) (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hR : IsSingularRiccati hD A ZA)
    (γ : ℝ) (hγ0 : 0 < γ) (hγα : γ < D.alpha P) (hγ2 : γ < 1 / 2)
    (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hcl : ClassFBSDE211 hD γ X B Y ZB ZY) (h210 : SolvesFBSDE211 hD A 1 0 X B Y ZB ZY)
    (h23 : SolvesFBSDE23 hD X Y ZY) :
    ∀ μ : ℝ≥0 → Ω → ℝ,
      IsCondExpVersion (filtF0 hD) P D.T (fun t ω => Y t ω / (2 * D.η t ω)) μ →
      IsOptimal hD μ (fun t ω => Y t ω / (2 * D.η t ω)) ∧
      (∀ t ≤ D.T, X t =ᵐ[P] stateOf D (fun t ω => Y t ω / (2 * D.η t ω)) t) ∧
      IsMFGSolution hD μ ∧
      (∃ V : Ω → ℝ, IsValue hD μ V) ∧
      ∀ V : Ω → ℝ, IsValue hD μ V →
        V =ᵐ[P] fun ω => A 0 ω * D.𝒳 ω ^ 2 / 2 + B 0 ω * D.𝒳 ω / 2 +
          (P[fun ω' => ∫ s in Set.Icc (0 : ℝ) D.T,
              D.κ s.toNNReal ω' * X s.toNNReal ω' * μ s.toNNReal ω' |
            MeasurableSpace.comap D.𝒳 inferInstance]) ω / 2 := by sorry

end MFGLiquidation.Equilibrium
