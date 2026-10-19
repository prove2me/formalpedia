-- Prove2me | Theorems.Thm_IncentiveAwarePricing_CORP_proposition_9_2
-- name    : IncentiveAwarePricing.CORP.proposition_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:14.973325+00:00
-- url     : https://prove2.me/theorems/8fa1bf42-3d8d-4104-850d-9ff6c4ce2ac6
-- title:
--   Proposition 9.2, p. 53 — per episode, utility-maximizing buyers lie O(log(ℓ/δ) + log(ℓN)/log(1/γ)) times and shade/overbid O(log(ℓN)/log(1/γ))
-- statement:
--   Fix $B_p>0$, $M>0$ and a noise density $f$ on $[-B_n,B_n]$ satisfying Assumption 1. There are constants $c_3,\dots,c_9$, depending only on $B_p,B_n,M,f$, with the following property. Take any $N\ge1$, $d\ge1$, discount factor $\gamma\in(0,1)$, feature law $\mathcal D$ on the unit ball of $\mathbb R^d$ whose second-moment matrix $\Sigma=\mathbb E[xx^\top]$ is positive definite (the standing assumption of p. 12, stated as $\mathbb E\langle x,u\rangle^2>0$ for $u\ne0$), preference vectors $\|\beta_i\|\le B_p$, measurable selections of CORP's estimator (8) and reserve rule (10), and a measurable strategy profile of utility-maximizing buyers whose bids are at most $M$ and pairwise distinct almost surely. Then for every episode $k\ge2$, every $\delta\in(0,1]$ and every buyer $i$:
--
--   1. with probability at least $1-(\delta+1)/\ell_{k-1}$,
--   $$|L_{ik}|\le c_3\log\frac{\ell_{k-1}}{\delta}+c_4\frac{\log\ell_{k-1}}{\log(1/\gamma)}+c_5\frac{\log N}{\log(1/\gamma)}; \tag{29}$$
--   2. with probability at least $1-1/\ell_{k-1}$,
--   $$\sum_{t\in E_{k-1}}s_{it}(1-q_{it})\le c_6\frac{\log\ell_{k-1}}{\log(1/\gamma)}+c_7\frac{\log N}{\log(1/\gamma)}; \tag{30}$$
--   3. with probability at least $1-1/\ell_{k-1}$,
--   $$\sum_{t\in E_{k-1}}o_{it}q_{it}\le c_8\frac{\log\ell_{k-1}}{\log(1/\gamma)}+c_9\frac{\log N}{\log(1/\gamma)}. \tag{31}$$
--
--   Here $L_{ik}$ is the set (27) of periods of episode $k-1$ in which buyer $i$ lies, $s_{it}$ and $o_{it}$ are his shading and overbidding, and all quantities are those of the play of CORP against the profile.
--
--   This is the step of the regret analysis that converts the buyers' impatience into a logarithmic bound on untruthful behaviour.
--
--   **Formalization Note** The eigenvalue bounds $c_{\min}/d$, $c_{\max}/d$ of the goal are not needed here (footnote 14: the constants depend on $B$ and $M$), but the positive definiteness of $\Sigma$ assumed on p. 12 is kept. The page allows $0\le\delta\le1$; at $\delta=0$ the bound $\log(\ell_{k-1}/\delta)$ is infinite, so $\delta\in(0,1]$ is used. "$i\in[N]$" is read per buyer, as the proof is per buyer. Logarithms are natural; Lean's episode index $e$ is $k-2$, so $\ell_{k-1}=2^e$. The proof (App. 14) treats the other buyers' bids as fixed under buyer $i$'s deviation, although their histories depend on it; the statement is not changed by that.
-- source:
--   Golrezaei, Javanmard, Mirrokni, Dynamic Incentive-Aware Learning: Robust Pricing in Contextual Auctions, arXiv:2002.11137v1, p. 53, Proposition 9.2, (29)–(31), footnote 14; (27) p. 51

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model
import Definitions.Def_IncentiveAwarePricing_CORP_Play

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace IncentiveAwarePricing.CORP

/-- **Proposition 9.2** (Bounding the Number of Lies), p. 53, (29)–(31). There are constants
`c₃, …, c₉`, depending only on `Bp, Bn, M, f`, such that for every instance, every
utility-maximizing profile, every feature law on the unit ball with positive definite second
moment matrix `Σ` (p. 12), every paper-episode `k = e + 2 ≥ 2` (so `ℓ_{k-1} = 2^e`), every
`δ ∈ (0, 1]` and every buyer `i`:
(29) `|L_ik| ≤ c₃ log(ℓ_{k-1}/δ) + c₄ log ℓ_{k-1}/log(1/γ) + c₅ log N/log(1/γ)` with probability
at least `1 - (δ + 1)/ℓ_{k-1}`;
(30) `∑_{t ∈ E_{k-1}} s_it (1 - q_it) ≤ c₆ log ℓ_{k-1}/log(1/γ) + c₇ log N/log(1/γ)` and
(31) `∑_{t ∈ E_{k-1}} o_it q_it ≤ c₈ log ℓ_{k-1}/log(1/γ) + c₉ log N/log(1/γ)`, each with
probability at least `1 - 1/ℓ_{k-1}`. -/
theorem proposition_9_2 (Bp Bn M : ℝ) (f : ℝ → ℝ)
    (hBp : 0 < Bp) (hM : 0 < M) (hf : NoiseStanding Bn f) (hA1 : Assumption1 Bn f) :
    ∃ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ,
      ∀ (N d : ℕ) (γ : ℝ), 1 ≤ N → 1 ≤ d → 0 < γ → γ < 1 →
      ∀ D : Measure (Ctx d), FeatureSupport d D →
        (∀ u : Ctx d, u ≠ 0 → 0 < ∫ x, ⟪x, u⟫ ^ 2 ∂D) →
      ∀ β : Fin N → Ctx d, (∀ i, ‖β i‖ ≤ Bp) →
      ∀ (est : Estimator N d) (res : ℝ → ℝ),
        IsCORPEstimator f Bp est → EstimatorMeasurable est →
        IsReserveRule f res → Measurable res →
      ∀ σ : Strategy N d, StrategyMeasurable σ →
        BidsBounded ⟨Bp, Bn, f, D, β, est, res⟩ M σ →
        BidsDistinct ⟨Bp, Bn, f, D, β, est, res⟩ σ →
        UtilityMaximizing ⟨Bp, Bn, f, D, β, est, res⟩ γ σ →
      ∀ (e : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ i : Fin N,
        ENNReal.ofReal (1 - (δ + 1) / 2 ^ e) ≤
          pathLaw (⟨Bp, Bn, f, D, β, est, res⟩ : Market N d) {ω |
            (lieCount ⟨Bp, Bn, f, D, β, est, res⟩ σ i e ω : ℝ) ≤
              c₃ * Real.log (2 ^ e / δ) + c₄ * Real.log (2 ^ e) / Real.log (1 / γ) +
                c₅ * Real.log N / Real.log (1 / γ)} ∧
        ENNReal.ofReal (1 - 1 / 2 ^ e) ≤
          pathLaw (⟨Bp, Bn, f, D, β, est, res⟩ : Market N d) {ω |
            ∑ n ∈ episodePeriods e,
                (record ⟨Bp, Bn, f, D, β, est, res⟩ σ ω n).shading i *
                  (1 - (record ⟨Bp, Bn, f, D, β, est, res⟩ σ ω n).alloc i) ≤
              c₆ * Real.log (2 ^ e) / Real.log (1 / γ) + c₇ * Real.log N / Real.log (1 / γ)} ∧
        ENNReal.ofReal (1 - 1 / 2 ^ e) ≤
          pathLaw (⟨Bp, Bn, f, D, β, est, res⟩ : Market N d) {ω |
            ∑ n ∈ episodePeriods e,
                (record ⟨Bp, Bn, f, D, β, est, res⟩ σ ω n).overbidding i *
                  (record ⟨Bp, Bn, f, D, β, est, res⟩ σ ω n).alloc i ≤
              c₈ * Real.log (2 ^ e) / Real.log (1 / γ) + c₉ * Real.log N / Real.log (1 / γ)} := by sorry

end IncentiveAwarePricing.CORP
