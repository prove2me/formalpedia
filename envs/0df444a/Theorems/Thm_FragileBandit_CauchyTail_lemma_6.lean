-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_lemma_6
-- name    : FragileBandit.CauchyTail.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:08.130417+00:00
-- url     : https://prove2.me/theorems/2da8d27c-a388-4676-a474-9988fc706582
-- title:
--   Lemma 6, Appendix D, p. 46 (corrected: D_inf(P_i, µ*(ν), M) < ∞) — sub-optimal arms are played infinitely often in probability
-- statement:
--   **Sub-optimal arms are sampled infinitely often.** Let $\mathcal M$ be a model: a set of probability laws on $\mathbb R$ with finite means. For a law $Q$ and $y \in \mathbb R$ let
--
--   $$D_{\inf}(Q,y,\mathcal M) = \inf\{D(Q\,\|\,Q') : Q' \in \mathcal M,\ \mu(Q') > y\},\qquad \inf\emptyset = +\infty \quad (29).$$
--
--   Let $f : (1,\infty)\to(0,\infty)$ be non-decreasing with $\liminf_{t\to\infty} f(t)/\log t \ge 1$ and $f(t) = o(t)$. Let $\mathcal E$ be a class of environments of $\mathcal M^K$ on which the algorithm $\pi$ satisfies, for every sub-optimal arm $i$,
--
--   $$\limsup_{T\to\infty}\frac{\log\mathbb P_{\nu\pi}(N_i(T) > T/K)}{f(T)} \le -1 \quad (31).$$
--
--   Let $\nu \in \mathcal E$ and let $i$ be a sub-optimal arm of $\nu$ such that replacing the law of arm $i$ by any $Q \in \mathcal M$ with mean above $\mu_*(\nu)$ gives an environment of $\mathcal E$ (automatic for $\mathcal E = \mathcal M^K$). If $D_{\inf}(P_i,\mu_*(\nu),\mathcal M) < \infty$, then $N_i(T) \to \infty$ in $\mathbb P_{\nu\pi}$-probability:
--
--   $$\lim_{T\to\infty}\mathbb P_{\nu\pi}\big(N_i(T) \le m\big) = 0\quad\text{for every } m \in \mathbb N.$$
--
--   Lemma 6 feeds the weak law of large numbers used in the proof of Theorem 4: the change of measure there needs the log-likelihood average over the plays of arm $i$, which requires many plays.
--
--   **Formalization Note** (31) is posed in power form: for every $a < 1$, eventually $\mathbb P_{\nu\pi}(N_i(T) > T/K) \le e^{-a f(T)}$. $D_{\inf}$ is the published `banditDInf`, valued in $[0,\infty]$.
--
--   Differences from the source:
--   - correction: no condition on D_inf(P_i, µ*(ν), M) → hypothesis D_inf(P_i, µ*(ν), M) < ∞; reason: the printed lemma is false: M = {δ_0, δ_1}, K = 2, f = log, ν = (δ_0, δ_1), and π plays each arm once, then forever the arm that paid 1; (31) holds on every environment of M² (a sub-optimal arm is played once) but N_1(T) = 1 for all T ≥ 2; the proof's step (85) needs P_i ≪ P_1 for some P_1 ∈ M with larger mean, which finite D_inf provides
--   - generalization: (31) assumed for every environment of M^K; conclusions for every environment of M^K → (31) assumed only on a class 𝓔 ⊆ M^K; conclusion for every ν ∈ 𝓔 such that replacing arm i by any Q ∈ M with mean above µ_*(ν) stays in 𝓔; reason: with 𝓔 = M^K the closure holds automatically and the statement is the printed one; with 𝓔 = the distinct-means environments of M_P^K it is what Theorem 1's proof needs (the replaced arm becomes the unique best arm)
--   - reading: f : (1, ∞) → (0, ∞) 'increasing' → f : ℝ → ℝ, positive and non-decreasing (MonotoneOn) on (1, ∞); reason: 'increasing' may mean strict or non-strict; the non-strict reading is the weaker hypothesis, hence the stronger theorem, and the proof (pp. 45–47) does not use monotonicity
--   - encoding: liminf_{t→∞} f(t)/log t ≥ 1 and f(t) = o(t); (31) limsup_T log P_νπ(N_i(T) > T/K)/f(T) ≤ −1 → ∀ a < 1, eventually a·log t ≤ f(t); f(t)/t → 0; (31) as ∀ a < 1, eventually P_νπ(N_i(T) > T/K) ≤ e^{−a f(T)}; reason: equivalent since f > 0 and log t > 0 for t > 1; the power form of (31) handles P = 0 (log 0 = −∞)
--   - encoding: a general model M of distributions on ℝ with finite means (p. 27); environments of M^K, ties allowed → M : Set (Measure ℝ) with every Q ∈ M a probability measure with ∫|x| dQ < ∞; environments are StochasticBandit K with every arm law in M; reason: the paper's model; the finite-mean condition makes banditDInf's Bochner mean the true mean
--   - encoding: P_νπ on ([K] × ℝ)^∞ (p. 7), events about N_i(T) → banditMeasure ν π T on the histories of the first T rounds (published BanditPolicy), N_i(T) = armPullCount i h; reason: the infinite-horizon law restricted to the first T rounds is exactly banditMeasure ν π T, and N_i(T) depends only on those rounds
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p. 46, Appendix D, Lemma 6 (assumptions of Theorem 4, p. 28, (31))

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- Lemma 6 (Appendix D, p. 46), corrected: under the assumptions of Theorem 4 (posed for a class `𝓔`
of environments of `M^K` on which (31) holds, closed under replacing arm `i` by a law of `M` whose mean
exceeds `µ_*(ν)`), for every `ν ∈ 𝓔` and every sub-optimal arm `i` with
`D_inf(P_i, µ_*(ν), M) < ∞`, `N_i(T) → ∞` in `P_νπ`-probability. -/
theorem lemma_6 {K : ℕ} (M : Set (Measure ℝ))
    (hM : ∀ Q ∈ M, IsProbabilityMeasure Q ∧ Integrable id Q)
    (f : ℝ → ℝ) (hf_pos : ∀ t : ℝ, 1 < t → 0 < f t) (hf_mono : MonotoneOn f (Set.Ioi 1))
    (hf_log : ∀ a : ℝ, a < 1 → ∀ᶠ t : ℝ in atTop, a * Real.log t ≤ f t)
    (hf_o : Tendsto (fun t : ℝ => f t / t) atTop (𝓝 0))
    (π : BanditPolicy K) (𝓔 : Set (StochasticBandit K))
    (h𝓔M : ∀ ν ∈ 𝓔, ∀ j, ν.P j ∈ M)
    (h31 : ∀ ν ∈ 𝓔, ∀ i, 0 < banditGap ν i → ∀ a : ℝ, a < 1 → ∀ᶠ T : ℕ in atTop,
      banditMeasure ν π T {h | (T : ℝ) / K < (armPullCount i h : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(a * f T))))
    (ν : StochasticBandit K) (hν : ν ∈ 𝓔) (i : Fin K) (hi : 0 < banditGap ν i)
    (hclosed : ∀ (Q : Measure ℝ) (hQ : IsProbabilityMeasure Q), Q ∈ M →
      banditOptimalMean ν < ∫ x, x ∂Q → replaceArm ν i Q hQ ∈ 𝓔)
    (hfin : banditDInf M (ν.P i) (banditOptimalMean ν) < ⊤) :
    ∀ m : ℕ, Tendsto (fun T : ℕ => banditMeasure ν π T {h | armPullCount i h ≤ m})
      atTop (𝓝 0) := by sorry

end FragileBandit.CauchyTail
