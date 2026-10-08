-- Prove2me | Theorems.Thm_MFGLiquidation_Nash_eq_3_5
-- name    : MFGLiquidation.Nash.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:18.564401+00:00
-- url     : https://prove2.me/theorems/6b2ab8a1-6ac4-4bc2-b56b-faa828a5cbc6
-- title:
--   (3.5) — the empirical mean of the equilibrium rates is within O(1/N) of µ* in conditional L²
-- statement:
--   In the setting of Lemma 3.2, let $\mu^*$ be a process with $\mu^*_t=\mathbb E[\xi^{*,j}_t\mid\mathcal F^0_t]$ for every player $j$ (as in (3.2)), let $C\ge0$ satisfy (3.3) for every player, and let $M$ be a positive measurable function with $\psi\le M$, i.e. $\mathbb E[\int_0^T|\xi^{*,j}_t|^2dt\mid\mathcal X^j]\le M(\mathcal X^j)$ a.s. for every $j$. Then for every $N\ge1$ and every player $i$ of the $N$-player game,
--   $$\mathbb E\Big[\int_0^T\Big(\mu^*_t-\frac1N\sum_{j=1}^N\xi^{*,j}_t\Big)^2dt\ \Big|\ \mathcal X^i\Big]\le\frac{2\big(M(\mathcal X^i)+(2N-1)C\big)}{N^2}\qquad\text{a.s.} \tag{3.5}$$
--
--   This is the propagation-of-chaos estimate behind Theorem 3.3: given player $i$'s own portfolio, the empirical average of the equilibrium rates is close to the mean-field rate, at the rate $O(1/\sqrt N)$ in conditional $L^2$.
--
--   **Formalization Note.** The paper proves (3.5) for player 1 "by the symmetry of the $N$ player game"; we state it for every player $i<N$ (players indexed from $0$, the sum over $j<N$). Conditioning on $\mathcal X^i=x^i$ is conditioning on $\sigma(\mathcal X^i)$, so the bound holds for $\nu$-a.e. $x^i$. "$\psi\le M$" is encoded through (3.4) as the a.s. inequality of conditional second moments. $C\ge0$ is made explicit (a bound on a nonnegative quantity), and $N\ge1$ is required. Assumption 2.3 per player is the paper's standing assumption.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 23, (3.5) in the proof of Theorem 3.3

import Mathlib
import Definitions.Def_MFGLiquidation_Nash_Setting
import Definitions.Def_MFGLiquidation_Nash_Game
import Definitions.Def_MFGLiquidation_Nash_Players

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

theorem eq_3_5
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
    ∀ N : ℕ, 1 ≤ N → ∀ i < N,
      P[fun ω => ∫ t in Set.Icc (0 : ℝ) Pop.T,
          (μ t.toNNReal ω - (1 / (N : ℝ)) * ∑ j ∈ Finset.range N, Pop.xiStar Yp j t.toNNReal ω) ^ 2
        | MeasurableSpace.comap (Pop.Xs i) inferInstance]
      ≤ᵐ[P] fun ω => 2 * (M (Pop.Xs i ω) + (2 * (N : ℝ) - 1) * C) / (N : ℝ) ^ 2 := by sorry

end MFGLiquidation.Nash
