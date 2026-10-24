-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_lemma_5
-- name    : FragileBandit.CauchyTail.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:00.516213+00:00
-- url     : https://prove2.me/theorems/bf4d5efc-79e3-43bb-a2aa-215bd7f1f13d
-- title:
--   Lemma 5, Appendix A, p. 39 (corrected: log g(n+1)/log g(n) → 1 in (ii), (iii)) — uniformizing the tail bounds over B_γ(T) = [g(T), (1−γ)T]
-- statement:
--   **Uniformization of tail bounds.** Let $\nu$ be any environment, $\pi$ any algorithm and $i$ an arm. Let $c > 0$, $\gamma \in (0,1)$, and let $g:(1,\infty)\to(0,\infty)$ be strictly increasing with $g(t)/\log t \to \infty$ and $g(t) = o(t)$. Write $B_\gamma(T) = [g(T),(1-\gamma)T]$.
--
--   1. (i) If
--   $$\liminf_{T\to\infty}\frac{\log\mathbb P_{\nu\pi}(N_i(T) > (1-\gamma)T)}{\log T} \ge -c \quad (48)$$
--   then
--   $$\liminf_{T\to\infty}\ \inf_{x\in B_\gamma(T)}\frac{\log\mathbb P_{\nu\pi}(N_i(T) > x)}{\log x} \ge -c. \quad (49)$$
--   2. (ii) Suppose in addition that $\log g(n+1)/\log g(n) \to 1$ as $n \to\infty$ through the integers. If
--   $$\limsup_{T\to\infty}\frac{\log\mathbb P_{\nu\pi}(N_i(T) > g(T))}{\log g(T)} \le -c \quad (50)$$
--   then
--   $$\limsup_{T\to\infty}\ \sup_{x\in B_\gamma(T)}\frac{\log\mathbb P_{\nu\pi}(N_i(T) > x)}{\log x} \le -c. \quad (51)$$
--   3. (iii) Under the same additional condition, (48) and (50) together give $\log\mathbb P_{\nu\pi}(N_i(T) > x)/\log x \to -c$ uniformly for $x \in B_\gamma(T)$.
--
--   Lemma 5 turns the bound (47) at the single point $x = (1-\gamma)T$ into the uniform bound (7) of Theorem 1 (with $g(t) = \log^{1+\gamma}t$), and with the Markov bound gives the two-sided limit (8) (with $g(t) = t^\gamma$); both choices of $g$ satisfy the additional condition.
--
--   **Formalization Note** Every log-ratio limit is in power form: (48) as $\forall a > c$, eventually $\mathbb P \ge T^{-a}$; (49) as $\forall a > c$, eventually $\mathbb P(N_i(T) > x) \ge x^{-a}$ for all $x\in B_\gamma(T)$; (50) and (51) likewise with $\le$ and $a < c$; (iii) as: for all $a < c < b$, eventually $x^{-b} \le \mathbb P(N_i(T) > x) \le x^{-a}$ on $B_\gamma(T)$. $g$ is a real function whose hypotheses are imposed on $(1,\infty)$.
--
--   Differences from the source:
--   - correction: (ii) and (iii) for any strictly increasing g with g/log → ∞ and g = o(t) → (ii) and (iii) additionally assume log g(n+1)/log g(n) → 1 along the integers; reason: false as printed: with a_k = 2^{2^k}, n_k = a_k², g(t) = a_k + (t − n_k)/(n_{k+1} − n_k) on [n_k, n_{k+1}), Gaussian arms and an algorithm playing arm i for the first Z rounds with P(Z > y) = a_k^{−c} on [a_k, a_{k+1}), (50) holds but at x = a_k^{1.5} the ratio is −2c/3 > −c, so (51) fails; the proof's step (54) needs log g(⌊g^{−1}(x)⌋) ≈ log x; g(t) = t^γ and g(t) = log^{1+γ}t, the two choices of Theorem 1, satisfy the condition
--   - generalization: 'let i be a sub-optimal arm in ν' → any arm i; reason: the proof (p. 40) uses only that t ↦ N_i(t) is non-decreasing; sub-optimal arms are a special case
--   - encoding: (iii) 'lim log P_νπ(N_i(T) > x)/log x = −c uniformly for x ∈ B_γ(T)' → for all a < c < b, eventually x^{−b} ≤ P_νπ(N_i(T) > x) ≤ x^{−a} for every x ∈ B_γ(T); reason: the power form of uniform convergence of the log-ratio, i.e. (49) and (51) together
--   - encoding: liminf / limsup / lim of log P_νπ(·)/log x (or /f(T)) as T → ∞, uniformly over the stated window → for every a beyond the exponent, eventually (for all x in the window) P_νπ(·) ≥ x^{−a} (resp. ≤ x^{−a}), probabilities compared in ℝ≥0∞; reason: equivalent for x > 1, the only regime that matters as the windows tend to infinity; it also gives P = 0 its intended meaning log 0 = −∞, where Lean's Real.log 0 = 0 would make a log-ratio statement true by junk
--   - encoding: g : (1, ∞) → (0, ∞) strictly increasing, lim g(t)/log t = ∞, g(t) = o(t) → g : ℝ → ℝ, StrictMonoOn on (1, ∞), positive on (1, ∞), g(t)/log t → ∞ and g(t)/t → 0 as t → ∞; reason: same functions; values off (1, ∞) are never used
--   - encoding: P_νπ on ([K] × ℝ)^∞ (p. 7), events about N_i(T) → banditMeasure ν π T on the histories of the first T rounds (published BanditPolicy), N_i(T) = armPullCount i h; reason: the infinite-horizon law restricted to the first T rounds is exactly banditMeasure ν π T, and N_i(T) depends only on those rounds
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p. 39, Appendix A, Lemma 5, (48)–(51); proof p. 40

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- Lemma 5 (Appendix A, p. 39), uniformization over `x ∈ B_γ(T) = [g(T), (1−γ)T]`, for any environment,
algorithm and arm, `c > 0`, `γ ∈ (0, 1)` and strictly increasing `g : (1, ∞) → (0, ∞)` with
`g(t)/log t → ∞` and `g(t) = o(t)`; every log-ratio limit in power form.
(i) (48) `⇒` (49).
(ii) (corrected: `log g(n+1) / log g(n) → 1`) (50) `⇒` (51).
(iii) (same correction) (48) and (50) `⇒` (49) and (51), i.e. `log P_νπ(N_i(T) > x)/log x → −c`
uniformly on `B_γ(T)`. -/
theorem lemma_5 {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (i : Fin K)
    (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (g : ℝ → ℝ) (hg_mono : StrictMonoOn g (Set.Ioi 1)) (hg_pos : ∀ t : ℝ, 1 < t → 0 < g t)
    (hg_log : Tendsto (fun t : ℝ => g t / Real.log t) atTop atTop)
    (hg_o : Tendsto (fun t : ℝ => g t / t) atTop (𝓝 0)) :
    -- (i): (48) ⇒ (49)
    ((∀ a : ℝ, c < a → ∀ᶠ T : ℕ in atTop, ENNReal.ofReal ((T : ℝ) ^ (-a)) ≤
        banditMeasure ν π T {h | (1 - γ) * (T : ℝ) < (armPullCount i h : ℝ)}) →
      ∀ a : ℝ, c < a → ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc (g T) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-a)) ≤ banditMeasure ν π T {h | x < (armPullCount i h : ℝ)}) ∧
    -- (ii): (50) ⇒ (51), corrected
    (Tendsto (fun n : ℕ => Real.log (g ((n : ℝ) + 1)) / Real.log (g n)) atTop (𝓝 1) →
      (∀ a : ℝ, a < c → ∀ᶠ T : ℕ in atTop,
        banditMeasure ν π T {h | g T < (armPullCount i h : ℝ)} ≤ ENNReal.ofReal (g T ^ (-a))) →
      ∀ a : ℝ, a < c → ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc (g T) ((1 - γ) * (T : ℝ)),
        banditMeasure ν π T {h | x < (armPullCount i h : ℝ)} ≤ ENNReal.ofReal (x ^ (-a))) ∧
    -- (iii): (48) and (50) ⇒ (49) and (51), corrected
    (Tendsto (fun n : ℕ => Real.log (g ((n : ℝ) + 1)) / Real.log (g n)) atTop (𝓝 1) →
      (∀ a : ℝ, c < a → ∀ᶠ T : ℕ in atTop, ENNReal.ofReal ((T : ℝ) ^ (-a)) ≤
        banditMeasure ν π T {h | (1 - γ) * (T : ℝ) < (armPullCount i h : ℝ)}) →
      (∀ a : ℝ, a < c → ∀ᶠ T : ℕ in atTop,
        banditMeasure ν π T {h | g T < (armPullCount i h : ℝ)} ≤ ENNReal.ofReal (g T ^ (-a))) →
      ∀ a b : ℝ, a < c → c < b → ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc (g T) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-b)) ≤ banditMeasure ν π T {h | x < (armPullCount i h : ℝ)} ∧
        banditMeasure ν π T {h | x < (armPullCount i h : ℝ)} ≤ ENNReal.ofReal (x ^ (-a))) := by sorry

end FragileBandit.CauchyTail
