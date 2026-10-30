-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_theorem_1
-- name    : FragileBandit.CauchyTail.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:56.262743+00:00
-- url     : https://prove2.me/theorems/b118d442-3c5d-489f-8e71-f962fba164e1
-- title:
--   Theorem 1, p. 10 — optimized bandit algorithms have truncated Cauchy regret tails
-- statement:
--   **Optimized algorithms have heavy, truncated Cauchy tails.** Let $P$ be a base distribution with $0$ in the interior of its natural parameter set $\Theta_P$, let $\pi$ be an $\mathcal M_P$-optimized algorithm (Definition 2), and let $\nu = (P^{\mu_1},\dots,P^{\mu_K}) \in \mathcal M_P^K$ have pairwise distinct means. For an arm $k$, let $r(1),\dots,r(i-1)$ be the arms with a larger mean, so that $k = r(i)$ is the $i$-th-best arm. For every $\gamma\in(0,1)$, with $B_\gamma(T) = [\log^{1+\gamma}T,(1-\gamma)T]$:
--
--   1. (7)
--   $$\liminf_{T\to\infty}\ \inf_{x\in B_\gamma(T)}\frac{\log\mathbb P_{\nu\pi}(N_{r(i)}(T) > x)}{\log x} \;\ge\; -\sum_{j=1}^{i-1}\ \inf_{z\in\mathcal I_P:\ z<\mu_{r(i)}}\frac{d_P(z,\mu_{r(j)})}{d_P(z,\mu_{r(i)})}.$$
--   2. (8) If $P$ is discrimination equivalent (Definition 3) and $k = r(2)$ is the second-best arm, then
--   $$\lim_{T\to\infty}\frac{\log\mathbb P_{\nu\pi}(N_{r(2)}(T) > x)}{\log x} = -1$$
--   uniformly for $x\in[T^\gamma,(1-\gamma)T]$.
--   3. If $P$ is discrimination equivalent, (7) holds with right side $-(i-1)$, for every $i$.
--
--   Since the regret is $R(T) = \sum_i N_i(T)\Delta_i$, (8) says the regret tail of every optimized algorithm decays like $x^{-1}$ up to the truncation at order $T$: logarithmic expected regret is achieved only with the heaviest tail compatible with it. This is the main result of the paper (abstract, p. 1; p. 4).
--
--   **Formalization Note** Every log-ratio limit is in power form: (7) as "for every real $a$ larger than the exponent, eventually $\mathbb P_{\nu\pi}(N_k(T) > x) \ge x^{-a}$ for all $x\in B_\gamma(T)$"; (8) as "for every $\epsilon > 0$, eventually $x^{-(1+\epsilon)} \le \mathbb P_{\nu\pi}(N_k(T) > x) \le x^{-(1-\epsilon)}$ on $[T^\gamma,(1-\gamma)T]$". The exponent is computed in $[0,\infty]$ with $\inf\emptyset = +\infty$, in which case (7) is vacuous. "Second-best" means exactly one arm has a larger mean.
--
--   Differences from the source:
--   - generalization: 'Moreover, for i ≥ 3, (7) holds with the right side equal to −(i−1)' → the third clause is stated for every arm k under discrimination equivalence, with i − 1 the number of arms of larger mean; reason: i ≥ 3 is the printed case; for i = 2 it is (7) with each summand equal to 1 under Definition 3, and for i = 1 the exponent is 0 and the claim is (7) for the best arm
--   - reading: Definition 2 quantifies over 'any environment ν ∈ M_P^K'; §2.1, p. 7: 'throughout the paper we will only consider environments where for each i … the i-th-best arm is unique' → IsOptimized and the environment ν range over environments of M_P^K with pairwise distinct means; reason: the paper's standing convention; on π it is the weaker hypothesis, so the stronger theorem, and r(i) is undefined with ties
--   - encoding: arms [K] = {1, …, K}; the i-th-best arm r(i); the arms r(1), …, r(i−1) → arms Fin K (paper's arm i is index i − 1); an arm k; the arms j with µ_j > µ_k; reason: with pairwise distinct means the arms with a larger mean than r(i) are exactly r(1), …, r(i−1), so i − 1 is their number; no ranking function is needed
--   - encoding: liminf / limsup / lim of log P_νπ(·)/log x (or /f(T)) as T → ∞, uniformly over the stated window → for every a beyond the exponent, eventually (for all x in the window) P_νπ(·) ≥ x^{−a} (resp. ≤ x^{−a}), probabilities compared in ℝ≥0∞; reason: equivalent for x > 1, the only regime that matters as the windows tend to infinity; it also gives P = 0 its intended meaning log 0 = −∞, where Lean's Real.log 0 = 0 would make a log-ratio statement true by junk
--   - encoding: the exponent Σ_j inf_{z ∈ I_P, z < µ_k} d_P(z, µ_j)/d_P(z, µ_k), with inf ∅ = +∞ → tailExponent in ℝ≥0∞ (empty infimum = ⊤); the clause 'for every a with tailExponent < a' is then vacuous when the exponent is ⊤, as a bound by −∞ is; reason: a real-valued sInf ∅ = 0 would turn the bound into the false 'P ≥ x^{−ε}' at an arm whose mean is min I_P
--   - encoding: Θ_P = {θ : Λ_P(θ) < ∞}; P^z = exp(θ_P(z)x − Λ_P(θ_P(z))) P(dx); I_P the means of these laws; d_P the KL divergence (3) → natParamSet P = {θ : x ↦ e^{θx} is P-integrable}; tilt = Measure.tilted; meanSet P requires a finite mean; θ_P(z) a choice of θ with mean z; dP = klDiv in ℝ≥0∞; reason: same sets and laws (Λ_P(θ) < ∞ iff e^{θx} is integrable; θ_P(z) is unique unless P is a point mass, where every tilt is P); avoids the junk value 0 of Mathlib's cgf at non-integrable θ
--   - encoding: P_νπ on ([K] × ℝ)^∞ (p. 7), events about N_i(T) → banditMeasure ν π T on the histories of the first T rounds (published BanditPolicy), N_i(T) = armPullCount i h; reason: the infinite-horizon law restricted to the first T rounds is exactly banditMeasure ν π T, and N_i(T) depends only on those rounds
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p. 10, Theorem 1, (7)–(8); proof Appendix A, pp. 38–39

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- Theorem 1 (p. 10): optimized bandit algorithms have truncated Cauchy regret tails. Let `π` be
`M_P`-optimized, `ν ∈ M_P^K` with distinct means, `k` any arm (the paper's `r(i)`) and `γ ∈ (0, 1)`.
(7) `liminf_T inf_{x ∈ [log^{1+γ} T, (1−γ)T]} log P_νπ(N_k(T) > x)/log x ≥ −tailExponent P ν k`.
(8) If `P` is discrimination equivalent and `k` is the second-best arm, then
`log P_νπ(N_k(T) > x)/log x → −1` uniformly for `x ∈ [T^γ, (1−γ)T]`.
Moreover, if `P` is discrimination equivalent, (7) holds with right side `−(i−1)`, where `i − 1` is the
number of arms with a larger mean than `k`.
All log-ratio limits are in power form (`P ≥ x^{−a}`, `P ≤ x^{−a}`). -/
theorem theorem_1 {K : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (π : BanditPolicy K) (hπ : IsOptimized P π)
    (ν : StochasticBandit K) (hν : IsModelEnv P ν) (hd : DistinctMeans ν) (k : Fin K)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    -- (7)
    (∀ a : ℝ, tailExponent P ν k < ENNReal.ofReal a → ∀ᶠ T : ℕ in atTop,
      ∀ x ∈ Set.Icc (Real.log T ^ (1 + γ)) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-a)) ≤ banditMeasure ν π T {h | x < (armPullCount k h : ℝ)}) ∧
    -- (8)
    (IsDiscEquiv P →
      (Finset.univ.filter (fun j => banditArmMean ν k < banditArmMean ν j)).card = 1 →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc ((T : ℝ) ^ γ) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-(1 + ε))) ≤ banditMeasure ν π T {h | x < (armPullCount k h : ℝ)} ∧
        banditMeasure ν π T {h | x < (armPullCount k h : ℝ)} ≤ ENNReal.ofReal (x ^ (-(1 - ε)))) ∧
    -- (7) with right side −(i − 1)
    (IsDiscEquiv P →
      ∀ a : ℝ, ((Finset.univ.filter (fun j => banditArmMean ν k < banditArmMean ν j)).card : ℝ) < a →
      ∀ᶠ T : ℕ in atTop, ∀ x ∈ Set.Icc (Real.log T ^ (1 + γ)) ((1 - γ) * (T : ℝ)),
        ENNReal.ofReal (x ^ (-a)) ≤ banditMeasure ν π T {h | x < (armPullCount k h : ℝ)}) := by sorry

end FragileBandit.CauchyTail
