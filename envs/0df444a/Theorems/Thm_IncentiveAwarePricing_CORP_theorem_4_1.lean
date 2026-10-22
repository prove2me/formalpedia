-- Prove2me | Theorems.Thm_IncentiveAwarePricing_CORP_theorem_4_1
-- name    : IncentiveAwarePricing.CORP.theorem_4_1
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:25.736853+00:00
-- url     : https://prove2.me/theorems/0eba2ffe-e952-45e8-9ae5-ba9afd69bf60
-- title:
--   Theorem 4.1, p. 23 — against utility-maximizing buyers CORP's T-period worst-case regret is O(Nd(log(Td) log T + log²T/log²(1/γ)))
-- statement:
--   Let $B_p,M,c_{\min},c_{\max}>0$ and let $f$ be a noise density on $[-B_n,B_n]$ whose distribution function $F$ satisfies Assumption 1 ($F$ and $1-F$ log-concave). Then there is a constant $C>0$, depending only on $B_p,B_n,M,f,c_{\min},c_{\max}$, such that the following holds for every number of buyers $N\ge1$, dimension $d\ge1$, horizon $T\ge2$ and discount factor $\gamma\in(0,1)$.
--
--   For every feature law $\mathcal D$ on the unit ball of $\mathbb R^d$ whose second-moment matrix has eigenvalues in $(c_{\min}/d,\,c_{\max}/d]$, every preference vectors $\beta_1,\dots,\beta_N$ with $\|\beta_i\|\le B_p$, every measurable selection of CORP's maximum-likelihood estimator (8) and of its reserve rule (10), and every measurable strategy profile of utility-maximizing buyers whose bids are at most $M$ and pairwise distinct almost surely, the regret of CORP against the benchmark of Proposition 3.1 satisfies
--   $$\mathrm{Regret}(T)=\sum_{t=1}^T(\mathrm{rev}^\star_t-\mathrm{rev}_t)\le C\,N\,d\Big(\log(Td)\log T+\frac{\log^2T}{\log^2(1/\gamma)}\Big).$$
--
--   The first term is the cost of learning the preference vectors from censored auction outcomes; the second is the cost of the buyers' strategic bidding, and it shrinks as the buyers become less patient.
--
--   **Formalization Note** The worst case (7) over $\beta$ and $\mathcal D$ is a universal quantifier, and $C$ is chosen before $N,d,T,\gamma$, the instance, the selections and the strategies. The following hypotheses are not in the theorem's text and are disclosed: the eigenvalue bounds on $\mathbb E[xx^\top]$ (used on pp. 57 and 72–73); bids at most $M$ (p. 14) and distinct (p. 20), which are model assumptions; measurability of strategies and selections; $N,d\ge1$; and $T\ge2$, since at $T=1$ the right side is $0$ while period $1$ is an exploration period. "Utility-maximizing" is pinned as: no buyer gains by switching to truthful bidding from the start of an episode on. Logarithms are natural. The paper's printed proof has gaps (Proposition 9.1 and Lemma 5, Appendix 13), and this statement is not claimed to follow from it.
-- source:
--   Golrezaei, Javanmard, Mirrokni, Dynamic Incentive-Aware Learning: Robust Pricing in Contextual Auctions, arXiv:2002.11137v1, p. 23, Theorem 4.1; (7) p. 17; proof App. 9, pp. 51–61

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model
import Definitions.Def_IncentiveAwarePricing_CORP_Play

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace IncentiveAwarePricing.CORP

/-- **Theorem 4.1** (Regret Bound: Known Noise Distribution), p. 23. Under Assumption 1, with the
noise distribution known, the `T`-period worst-case regret of CORP against utility-maximizing
buyers is `O(N d (log(T d) log T + log² T / log²(1/γ)))`. The constant `C` depends only on
`Bp, Bn, M, f, c_min, c_max`. -/
theorem theorem_4_1 (Bp Bn M cmin cmax : ℝ) (f : ℝ → ℝ)
    (hBp : 0 < Bp) (hM : 0 < M) (hcmin : 0 < cmin) (hcmax : 0 < cmax)
    (hf : NoiseStanding Bn f) (hA1 : Assumption1 Bn f) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N d T : ℕ) (γ : ℝ), 1 ≤ N → 1 ≤ d → 2 ≤ T → 0 < γ → γ < 1 →
      ∀ D : Measure (Ctx d), FeatureLaw d cmin cmax D →
      ∀ β : Fin N → Ctx d, (∀ i, ‖β i‖ ≤ Bp) →
      ∀ (est : Estimator N d) (res : ℝ → ℝ),
        IsCORPEstimator f Bp est → EstimatorMeasurable est →
        IsReserveRule f res → Measurable res →
      ∀ σ : Strategy N d, StrategyMeasurable σ →
        BidsBounded ⟨Bp, Bn, f, D, β, est, res⟩ M σ →
        BidsDistinct ⟨Bp, Bn, f, D, β, est, res⟩ σ →
        UtilityMaximizing ⟨Bp, Bn, f, D, β, est, res⟩ γ σ →
        regret ⟨Bp, Bn, f, D, β, est, res⟩ σ T ≤
          C * N * d * (Real.log (T * d) * Real.log T +
            Real.log T ^ 2 / Real.log (1 / γ) ^ 2) := by sorry

end IncentiveAwarePricing.CORP
