-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_markov_tail_bound
-- name    : FragileBandit.CauchyTail.markov_tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:44.266667+00:00
-- url     : https://prove2.me/theorems/221e574d-ba0c-4d6c-bbcc-2a348d95d199
-- title:
--   Appendix A, p. 38 — Markov tail bound: limsup log P(N_i(T) > c·T^γ)/log T^γ ≤ −1 for M_P-optimized algorithms
-- statement:
--   **The tail of an optimized algorithm is no heavier than truncated Cauchy.** Let $P$ be a base distribution with $0$ in the interior of $\Theta_P$, let $\pi$ be $\mathcal M_P$-optimized (Definition 2), let $\nu \in \mathcal M_P^K$ have pairwise distinct means and let $i$ be a sub-optimal arm. For every $\gamma \in (0,1]$ and $c > 0$,
--
--   $$\limsup_{T\to\infty}\frac{\log \mathbb P_{\nu\pi}\big(N_i(T) > cT^\gamma\big)}{\log(T^\gamma)} \le -1.$$
--
--   On p. 38 this is the bound for the second-best arm with $c = 1$, obtained from Definition 2 and Markov's inequality; it is part (ii)'s hypothesis (50) of Lemma 5 for $g(t) = t^\gamma$. With $c = 1/K$ and $\gamma = 1$ it is (31) of Theorem 4 for $f = \log$, the condition Remark 3 calls "automatically satisfied" for optimized algorithms.
--
--   **Formalization Note** The limsup is posed in power form: for every $a < 1$, eventually $\mathbb P_{\nu\pi}(N_i(T) > cT^\gamma) \le (T^\gamma)^{-a}$.
--
--   Differences from the source:
--   - generalization: the second-best arm (arm 2), threshold T^γ, γ ∈ (0, 1) → every sub-optimal arm i, threshold c·T^γ for any c > 0, γ ∈ (0, 1]; reason: c = 1, i = 2, γ ∈ (0, 1) is the printed display; c = 1/K, γ = 1 gives (31) with f = log, which the chain to Theorem 1 needs
--   - reading: Definition 2 quantifies over 'any environment ν ∈ M_P^K'; §2.1, p. 7: 'throughout the paper we will only consider environments where for each i … the i-th-best arm is unique' → IsOptimized and the environment ν range over environments of M_P^K with pairwise distinct means; reason: the paper's standing convention; on π it is the weaker hypothesis, so the stronger theorem, and r(i) is undefined with ties
--   - encoding: liminf / limsup / lim of log P_νπ(·)/log x (or /f(T)) as T → ∞, uniformly over the stated window → for every a beyond the exponent, eventually (for all x in the window) P_νπ(·) ≥ x^{−a} (resp. ≤ x^{−a}), probabilities compared in ℝ≥0∞; reason: equivalent for x > 1, the only regime that matters as the windows tend to infinity; it also gives P = 0 its intended meaning log 0 = −∞, where Lean's Real.log 0 = 0 would make a log-ratio statement true by junk
--   - encoding: Θ_P = {θ : Λ_P(θ) < ∞}; P^z = exp(θ_P(z)x − Λ_P(θ_P(z))) P(dx); I_P the means of these laws; d_P the KL divergence (3) → natParamSet P = {θ : x ↦ e^{θx} is P-integrable}; tilt = Measure.tilted; meanSet P requires a finite mean; θ_P(z) a choice of θ with mean z; dP = klDiv in ℝ≥0∞; reason: same sets and laws (Λ_P(θ) < ∞ iff e^{θx} is integrable; θ_P(z) is unique unless P is a point mass, where every tilt is P); avoids the junk value 0 of Mathlib's cgf at non-integrable θ
--   - encoding: P_νπ on ([K] × ℝ)^∞ (p. 7), events about N_i(T) → banditMeasure ν π T on the histories of the first T rounds (published BanditPolicy), N_i(T) = armPullCount i h; reason: the infinite-horizon law restricted to the first T rounds is exactly banditMeasure ν π T, and N_i(T) depends only on those rounds
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p. 38, Appendix A, display after (47) ('using Markov's inequality')

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- Markov tail bound (Appendix A, p. 38): for an `M_P`-optimized algorithm, every environment
`ν ∈ M_P^K` with distinct means and every sub-optimal arm `i`,
`limsup_{T→∞} log P_νπ(N_i(T) > c T^γ) / log(T^γ) ≤ −1`, here for any threshold `c T^γ` with `c > 0`,
`γ ∈ (0, 1]` (the page has `c = 1`, `γ ∈ (0, 1)`), in power form: for every `a < 1`, eventually
`P_νπ(N_i(T) > c T^γ) ≤ (T^γ)^{−a}`. -/
theorem markov_tail_bound {K : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (π : BanditPolicy K) (hπ : IsOptimized P π)
    (ν : StochasticBandit K) (hν : IsModelEnv P ν) (hd : DistinctMeans ν)
    (i : Fin K) (hi : 0 < banditGap ν i) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) 1)
    (c : ℝ) (hc : 0 < c) :
    ∀ a : ℝ, a < 1 → ∀ᶠ T : ℕ in atTop,
      banditMeasure ν π T {h | c * (T : ℝ) ^ γ < (armPullCount i h : ℝ)} ≤
        ENNReal.ofReal (((T : ℝ) ^ γ) ^ (-a)) := by sorry

end FragileBandit.CauchyTail
