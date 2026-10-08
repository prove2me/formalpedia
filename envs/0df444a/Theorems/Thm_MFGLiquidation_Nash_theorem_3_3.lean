-- Prove2me | Theorems.Thm_MFGLiquidation_Nash_theorem_3_3
-- name    : MFGLiquidation.Nash.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:26.751239+00:00
-- url     : https://prove2.me/theorems/cc2eed9d-f91c-48d5-b7b5-853adf6ec242
-- title:
--   Theorem 3.3 — the mean-field strategies form an O(1/√N)-Nash equilibrium of the N-player liquidation game
-- statement:
--   Consider the $N$-player portfolio liquidation game with common noise $W^0$, private noises $W^i$ and i.i.d. initial portfolios $\mathcal X^i$ with law $\nu$, under Assumption 3.1 (the cost coefficients $\kappa^i,\eta^i,\lambda^i$ are the same nonnegative bounded measurable functionals of $(t,\mathcal X^i,W^i_{\cdot\wedge t},W^0_{\cdot\wedge t})$ for every player) and the standing Assumption 2.3 for every player. For each player $i$ let $(X^i,Y^i,Z^i)$ solve the FBSDE (2.3) for player $i$'s data in the class of Theorem 2.4, and let $\xi^{*,i}=Y^i/(2\eta^i)$ be the resulting mean-field strategy. Let $M$ be a positive measurable function with $\psi\le M$, where $\psi(\mathcal X^i)=\mathbb E[\int_0^T|\xi^{*,i}_t|^2dt\mid\mathcal X^i]$ as in (3.4), and let player $i$'s admissible set be
--   $$\mathcal A^i=\Big\{\xi\in\mathcal A_{\mathbb F^i}(\mathcal X^i):\ \mathbb E\Big[\int_0^T|\xi_t|^2dt\ \Big|\ \mathcal X^i\Big]\le M(\mathcal X^i)\Big\}.$$
--   Then there is a real function $g$, independent of the player and of $N$, such that for every $N\ge1$, every player $i$ of the $N$-player game and every $\xi^i\in\mathcal A^i$,
--   $$J^{N,i}(\vec\xi^*)\le J^{N,i}(\xi^i,\xi^{*,-i})+\frac{g(\mathcal X^i)}{\sqrt N}\qquad\text{a.s.},$$
--   where $J^{N,i}$ is the conditional cost (1.4) and $(\xi^i,\xi^{*,-i})$ is the profile $\vec\xi^*$ with player $i$'s strategy replaced by $\xi^i$.
--
--   So no player can lower her conditional expected cost by more than $O(1/\sqrt N)$ by deviating unilaterally from the strategies derived from the mean field game: the mean-field equilibrium is an approximate Nash equilibrium of the finite game.
--
--   **Formalization Note.** Players are indexed from $0$ ($i<N$ is the paper's $1\le i\le N$), and only strategies $j<N$ enter $J^{N,i}$; the average in $J^{N,i}$ includes the deviating player's own strategy. Assumption 2.3 for each player is added from the paper's standing assumption (p. 8); the proof uses Propositions 2.8 and 2.9, which need it. The paper's "$O(1/\sqrt N)$ to be interpreted as $g(x_i)/\sqrt N$ for some real-valued function $g$ independent of $i$" is stated with $g$ quantified before $N$ and $i$. Conditioning on $\mathcal X^i=x^i$ is conditioning on $\sigma(\mathcal X^i)$, so the inequality holds for $\nu$-a.e. $x^i$; "$\psi\le M$" is the a.s. inequality of the conditional second moments. Measurability of $M$ is added so that $M(\mathcal X^i)$ is a random variable. The deviation $\xi$ is progressive for player $i$'s own filtration $\mathbb F^i$ and satisfies the liquidation constraint $\int_0^T\xi_t\,dt=\mathcal X^i$.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 22–23, Theorem 3.3 (with (1.4) p. 4, Assumption 3.1 p. 21, (3.4) p. 22)

import Mathlib
import Definitions.Def_MFGLiquidation_Nash_Setting
import Definitions.Def_MFGLiquidation_Nash_Game
import Definitions.Def_MFGLiquidation_Nash_Players

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

theorem theorem_3_3
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (Pop : Population Ω k) (ν : Measure ℝ) (hstd : Pop.Standing P ν)
    (h31 : Pop.Assumption31)
    (h23 : ∀ i, (Pop.player i).Assumption23 P (hstd.player i))
    (Xp Yp : ℕ → ℝ≥0 → Ω → ℝ) (Zp : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (hsol : ∀ i, SolvesFBSDE23InClass (hstd.player i) (Xp i) (Yp i) (Zp i))
    (M : ℝ → ℝ) (hM : Measurable M) (hMpos : ∀ x, 0 < M x)
    (hψM : ∀ i, P[fun ω => ∫ t in Set.Icc (0 : ℝ) Pop.T, Pop.xiStar Yp i t.toNNReal ω ^ 2
      | MeasurableSpace.comap (Pop.Xs i) inferInstance] ≤ᵐ[P] fun ω => M (Pop.Xs i ω)) :
    ∃ g : ℝ → ℝ, ∀ N : ℕ, 1 ≤ N → ∀ i < N, ∀ ξ : ℝ≥0 → Ω → ℝ, Pop.AdmN hstd M i ξ →
      Pop.costN P N i (Pop.xiStar Yp)
        ≤ᵐ[P] fun ω => Pop.costN P N i (Function.update (Pop.xiStar Yp) i ξ) ω
          + g (Pop.Xs i ω) / Real.sqrt N := by sorry

end MFGLiquidation.Nash
