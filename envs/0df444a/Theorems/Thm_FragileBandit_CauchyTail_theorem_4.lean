-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_theorem_4
-- name    : FragileBandit.CauchyTail.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:51.872537+00:00
-- url     : https://prove2.me/theorems/53887a05-464d-44ef-8b54-16e9610e81ac
-- title:
--   Theorem 4, p. 28 — a regret tail decaying like e^{−f(T)} forces N_i(T) ≳ f(T)/D_inf: the one-sided WLLN (32) and the bound (33)
-- statement:
--   **Trade-off between regret tail and expected regret.** Let $\mathcal M$ be a model (probability laws on $\mathbb R$ with finite means) and $D_{\inf}$ as in (29). Let $f : (1,\infty)\to(0,\infty)$ be non-decreasing with $\liminf_{t\to\infty} f(t)/\log t \ge 1$ and $f(t) = o(t)$. Suppose the algorithm $\pi$ satisfies, on every environment $\nu$ of a class $\mathcal E \subseteq \mathcal M^K$ and for every sub-optimal arm $i$ of $\nu$,
--
--   $$\limsup_{T\to\infty}\frac{\log\mathbb P_{\nu\pi}(N_i(T) > T/K)}{f(T)} \le -1 \quad (31).$$
--
--   Let $\nu \in \mathcal E$ and let $i$ be a sub-optimal arm such that replacing arm $i$ by any $Q \in \mathcal M$ with mean above $\mu_*(\nu)$ stays in $\mathcal E$ (automatic for $\mathcal E = \mathcal M^K$). Then for every $\epsilon \in (0,1)$
--
--   $$\lim_{T\to\infty}\mathbb P_{\nu\pi}\Big(\frac{N_i(T)}{f(T)} \ge \frac{1-\epsilon}{D_{\inf}(P_i,\mu_*(\nu),\mathcal M)}\Big) = 1 \quad (32)$$
--
--   and
--
--   $$\liminf_{T\to\infty}\frac{\mathbb E_{\nu\pi}[N_i(T)]}{f(T)} \ge \frac{1}{D_{\inf}(P_i,\mu_*(\nu),\mathcal M)} \quad (33).$$
--
--   With $f = \log$, (31) holds for consistent algorithms and (33) is the Burnetas–Katehakis generalization of the Lai–Robbins lower bound; faster-growing $f$ (lighter regret tails) force proportionally larger expected regret.
--
--   **Formalization Note** (32) and (33) are read in $[0,\infty]$: for every real $c$ with $c\cdot D_{\inf}(P_i,\mu_*(\nu),\mathcal M) < 1$, $\mathbb P_{\nu\pi}(N_i(T) \ge c f(T)) \to 1$, and eventually $c f(T) \le \mathbb E_{\nu\pi}[N_i(T)]$. For $D_{\inf} \in (0,\infty)$ these are exactly (32) for every $\epsilon$ and the liminf bound (33); for $D_{\inf} = \infty$ they are trivial, and for $D_{\inf} = 0$ they read $1/0 = \infty$, as the proof gives. (31) is in power form, as in Lemma 6.
--
--   Differences from the source:
--   - generalization: (31) assumed for every environment of M^K; conclusions for every environment of M^K → (31) assumed only on a class 𝓔 ⊆ M^K; conclusion for every ν ∈ 𝓔 such that replacing arm i by any Q ∈ M with mean above µ_*(ν) stays in 𝓔; reason: with 𝓔 = M^K the closure holds automatically and the statement is the printed one; with 𝓔 = the distinct-means environments of M_P^K it is what Theorem 1's proof needs (the replaced arm becomes the unique best arm)
--   - reading: (32) with the factor (1−ε)/D_inf for ε ∈ (0, 1), and (33) with 1/D_inf, where D_inf may be 0 or +∞ → for every real c with ofReal c · D_inf < 1 (in ℝ≥0∞): P_νπ(c f(T) ≤ N_i(T)) → 1, and eventually c f(T) ≤ E_νπ[N_i(T)]; reason: identical to the page for D_inf ∈ (0, ∞) (c ranges over (1−ε)/D_inf and everything below); trivial for D_inf = ∞; for D_inf = 0 it is the convention 1/0 = ∞, which the proof (79)–(83) gives
--   - reading: f : (1, ∞) → (0, ∞) 'increasing' → f : ℝ → ℝ, positive and non-decreasing (MonotoneOn) on (1, ∞); reason: 'increasing' may mean strict or non-strict; the non-strict reading is the weaker hypothesis, hence the stronger theorem, and the proof (pp. 45–47) does not use monotonicity
--   - encoding: liminf_{t→∞} f(t)/log t ≥ 1 and f(t) = o(t); (31) limsup_T log P_νπ(N_i(T) > T/K)/f(T) ≤ −1 → ∀ a < 1, eventually a·log t ≤ f(t); f(t)/t → 0; (31) as ∀ a < 1, eventually P_νπ(N_i(T) > T/K) ≤ e^{−a f(T)}; reason: equivalent since f > 0 and log t > 0 for t > 1; the power form of (31) handles P = 0 (log 0 = −∞)
--   - encoding: a general model M of distributions on ℝ with finite means (p. 27); environments of M^K, ties allowed → M : Set (Measure ℝ) with every Q ∈ M a probability measure with ∫|x| dQ < ∞; environments are StochasticBandit K with every arm law in M; reason: the paper's model; the finite-mean condition makes banditDInf's Bochner mean the true mean
--   - encoding: P_νπ on ([K] × ℝ)^∞ (p. 7), events about N_i(T) → banditMeasure ν π T on the histories of the first T rounds (published BanditPolicy), N_i(T) = armPullCount i h; reason: the infinite-horizon law restricted to the first T rounds is exactly banditMeasure ν π T, and N_i(T) depends only on those rounds
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p. 28, §5.2, Theorem 4, (31)–(33); proof Appendix D, pp. 45–46

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- Theorem 4 (§5.2, p. 28): for a general model `M` (probability laws on `ℝ` with finite means), an
increasing `f : (1, ∞) → (0, ∞)` with `liminf f(t)/log t ≥ 1` and `f(t) = o(t)`, and an algorithm `π`
satisfying (31), `limsup_T log P_νπ(N_i(T) > T/K) / f(T) ≤ −1`, for every environment of a class `𝓔 ⊆ M^K`
and every sub-optimal arm, the following hold for every `ν ∈ 𝓔` closed under replacing arm `i` by a law of
`M` with mean above `µ_*(ν)` (for `𝓔 = M^K` this closure is automatic), and every sub-optimal arm `i`:
(32) `P_νπ(N_i(T)/f(T) ≥ c) → 1` for every `c` with `c · D_inf(P_i, µ_*(ν), M) < 1`, and
(33) `liminf E_νπ[N_i(T)]/f(T) ≥ 1/D_inf(P_i, µ_*(ν), M)`, i.e. eventually `c f(T) ≤ E_νπ[N_i(T)]` for
every such `c`. -/
theorem theorem_4 {K : ℕ} (M : Set (Measure ℝ))
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
      banditOptimalMean ν < ∫ x, x ∂Q → replaceArm ν i Q hQ ∈ 𝓔) :
    (∀ c : ℝ, ENNReal.ofReal c * banditDInf M (ν.P i) (banditOptimalMean ν) < 1 →
      Tendsto (fun T : ℕ => banditMeasure ν π T {h | c * f T ≤ (armPullCount i h : ℝ)})
        atTop (𝓝 1)) ∧
    (∀ c : ℝ, ENNReal.ofReal c * banditDInf M (ν.P i) (banditOptimalMean ν) < 1 →
      ∀ᶠ T : ℕ in atTop, c * f T ≤ expPulls ν π T i) := by sorry

end FragileBandit.CauchyTail
