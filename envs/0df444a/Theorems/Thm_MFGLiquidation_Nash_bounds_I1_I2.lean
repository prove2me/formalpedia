-- Prove2me | Theorems.Thm_MFGLiquidation_Nash_bounds_I1_I2
-- name    : MFGLiquidation.Nash.bounds_I1_I2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:20.620584+00:00
-- url     : https://prove2.me/theorems/c98e6d67-5671-4fc6-b641-b4dc75df3e96
-- title:
--   Proof of Theorem 3.3, p. 24 — the bounds on |I₁| and I₂ of order 1/√N
-- statement:
--   In the setting of (3.5) (a common conditional mean $\mu^*$, a constant $C\ge0$ satisfying (3.3) for all players, and a positive measurable $M$ with $\psi\le M$), let $N\ge1$, let $i$ be a player of the $N$-player game and let $\xi\in\mathcal A^i$ be a deviation, i.e. $\xi\in\mathcal A_{\mathbb F^i}(\mathcal X^i)$ with $\mathbb E[\int_0^T|\xi_t|^2dt\mid\mathcal X^i]\le M(\mathcal X^i)$. Write $M=M(\mathcal X^i)$ and $\kappa_{\max}=\operatorname{ess\,sup}\kappa^i$. Then, almost surely,
--   $$|I_1|\le\frac{M\kappa_{\max}T}{N}+\frac{2\kappa_{\max}T\sqrt M}{N}\Big(\sqrt M+\sqrt{2\big(M+(2N-1)C\big)}\Big),$$
--   $$|I_2|\le\frac{2\kappa_{\max}T\sqrt M\sqrt{M+(2N-1)C}}{N},$$
--   where $I_1=I_1(\xi)$ and $I_2$ are the two differences of conditional costs of the proof of Theorem 3.3 (see the definition file).
--
--   Since $J^{N,i}(\xi,\xi^{*,-i})-J^{N,i}(\vec\xi^*)\ge I_1+I_2$ by the optimality of $\xi^{*,i}$ against $\mu^*$, these two bounds, both of order $1/\sqrt N$, give Theorem 3.3.
--
--   **Formalization Note.** The paper prints the first bound for $\sup_{\xi\in\mathcal A^1}|I_1|$; we state it for every $\xi\in\mathcal A^i$, which is equivalent. The paper prints "$I_2\le\dots$" but its Cauchy–Schwarz step bounds $|I_2|$, and the proof of Theorem 3.3 uses the lower bound on $I_2$; we state the bound for $|I_2|$. The printed constants are kept even though they are not sharp. The paper writes the bounds for player 1; we state them for every player $i<N$ (players indexed from $0$). $\kappa_{\max}$ is the essential supremum of $\kappa^i$ over $[0,T]\times\Omega$. Assumption 2.3 per player is the paper's standing assumption.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 24, proof of Theorem 3.3, bounds on sup|I₁| and I₂

import Mathlib
import Definitions.Def_MFGLiquidation_Nash_Setting
import Definitions.Def_MFGLiquidation_Nash_Game
import Definitions.Def_MFGLiquidation_Nash_Players

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

theorem bounds_I1_I2
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (Pop : Population Ω k) (ν : Measure ℝ) (hstd : Pop.Standing P ν)
    (h31 : Pop.Assumption31)
    (h23 : ∀ i, (Pop.player i).Assumption23 P (hstd.player i))
    (Xp Yp : ℕ → ℝ≥0 → Ω → ℝ) (Zp : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hsol : ∀ i, SolvesFBSDE23InClass (hstd.player i) (Xp i) (Yp i) (Zp i))
    (M : ℝ → ℝ) (hM : Measurable M) (hMpos : ∀ x, 0 < M x)
    (hψM : ∀ i, P[fun ω => ∫ t in Set.Icc (0 : ℝ) Pop.T, Pop.xiStar Yp i t.toNNReal ω ^ 2
      | MeasurableSpace.comap (Pop.Xs i) inferInstance] ≤ᵐ[P] fun ω => M (Pop.Xs i ω))
    (μ : ℝ≥0 → Ω → ℝ)
    (hμ : ∀ i, IsCondExpVersion (filtF0 (hstd.player i)) P Pop.T (Pop.xiStar Yp i) μ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ j, ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) Pop.T, ‖Pop.xiStar Yp j t.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal C) :
    ∀ N : ℕ, 1 ≤ N → ∀ i < N, ∀ ξ : ℝ≥0 → Ω → ℝ, Pop.AdmN hstd M i ξ →
      (∀ᵐ ω ∂P, |Pop.I1 P N i μ Yp ξ ω|
        ≤ M (Pop.Xs i ω) * (Pop.player i).kappaMax P * Pop.T / N
          + 2 * (Pop.player i).kappaMax P * Pop.T * Real.sqrt (M (Pop.Xs i ω)) / N
            * (Real.sqrt (M (Pop.Xs i ω))
              + Real.sqrt (2 * (M (Pop.Xs i ω) + (2 * (N : ℝ) - 1) * C)))) ∧
      (∀ᵐ ω ∂P, |Pop.I2 P N i μ Yp ω|
        ≤ 2 * (Pop.player i).kappaMax P * Pop.T * Real.sqrt (M (Pop.Xs i ω))
          * Real.sqrt (M (Pop.Xs i ω) + (2 * (N : ℝ) - 1) * C) / N) := by sorry

end MFGLiquidation.Nash
