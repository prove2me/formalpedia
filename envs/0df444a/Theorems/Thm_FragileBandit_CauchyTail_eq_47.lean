-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_eq_47
-- name    : FragileBandit.CauchyTail.eq_47
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:53.08603+00:00
-- url     : https://prove2.me/theorems/0a06a179-e921-4877-8a55-4ad7e64254b9
-- title:
--   (47), Appendix A, p. 38 — liminf log P(N_k(T) > (1−γ)T)/log T ≥ −Σ_{j: µ_j > µ_k} inf_z d_P(z, µ_j)/d_P(z, µ_k), for every arm
-- statement:
--   **Tail lower bound at the right end of the window.** Let $P$ be a base distribution with $0$ in the interior of $\Theta_P$, $\pi$ an $\mathcal M_P$-optimized algorithm, $\nu \in \mathcal M_P^K$ with pairwise distinct means, $k$ an arm with mean $\mu_k$, and $\gamma\in(0,1)$. Then
--
--   $$\liminf_{T\to\infty}\frac{\log\mathbb P_{\nu\pi}\big(N_k(T) > (1-\gamma)T\big)}{\log T} \;\ge\; -\sum_{j:\ \mu_j>\mu_k}\ \inf_{z\in\mathcal I_P:\ z<\mu_k}\frac{d_P(z,\mu_j)}{d_P(z,\mu_k)},$$
--
--   with $\inf\emptyset = +\infty$. For the second-best arm the sum has the single term of (47); for the $i$-th-best arm, $i \ge 3$, it is the bound the paper obtains on p. 39 "through arguments analogous to those in (43)–(47)"; for the best arm the sum is empty. Lemma 5(i) then extends this bound from $x = (1-\gamma)T$ to the whole window $x \in [\log^{1+\gamma}T,(1-\gamma)T]$ of Theorem 1.
--
--   **Formalization Note** Power form: for every real $a$ larger than the exponent (computed in $[0,\infty]$), eventually $\mathbb P_{\nu\pi}(N_k(T) > (1-\gamma)T) \ge T^{-a}$; when the exponent is $+\infty$ the statement is vacuous.
--
--   Differences from the source:
--   - generalization: (47) for the second-best arm (p. 38); the case i ≥ 3 stated as 'analogous' (p. 39) → every arm k, with exponent Σ over the arms of larger mean; reason: k = r(2) is (47) and k = r(i), i ≥ 3, is the p. 39 claim; for the best arm the exponent is 0 and the bound says P(N_k(T) > (1−γ)T) is not polynomially small, which holds because the other arms are played O(log T) times in expectation
--   - reading: Definition 2 quantifies over 'any environment ν ∈ M_P^K'; §2.1, p. 7: 'throughout the paper we will only consider environments where for each i … the i-th-best arm is unique' → IsOptimized and the environment ν range over environments of M_P^K with pairwise distinct means; reason: the paper's standing convention; on π it is the weaker hypothesis, so the stronger theorem, and r(i) is undefined with ties
--   - encoding: arms [K] = {1, …, K}; the i-th-best arm r(i); the arms r(1), …, r(i−1) → arms Fin K (paper's arm i is index i − 1); an arm k; the arms j with µ_j > µ_k; reason: with pairwise distinct means the arms with a larger mean than r(i) are exactly r(1), …, r(i−1), so i − 1 is their number; no ranking function is needed
--   - encoding: liminf / limsup / lim of log P_νπ(·)/log x (or /f(T)) as T → ∞, uniformly over the stated window → for every a beyond the exponent, eventually (for all x in the window) P_νπ(·) ≥ x^{−a} (resp. ≤ x^{−a}), probabilities compared in ℝ≥0∞; reason: equivalent for x > 1, the only regime that matters as the windows tend to infinity; it also gives P = 0 its intended meaning log 0 = −∞, where Lean's Real.log 0 = 0 would make a log-ratio statement true by junk
--   - encoding: the exponent Σ_j inf_{z ∈ I_P, z < µ_k} d_P(z, µ_j)/d_P(z, µ_k), with inf ∅ = +∞ → tailExponent in ℝ≥0∞ (empty infimum = ⊤); the clause 'for every a with tailExponent < a' is then vacuous when the exponent is ⊤, as a bound by −∞ is; reason: a real-valued sInf ∅ = 0 would turn the bound into the false 'P ≥ x^{−ε}' at an arm whose mean is min I_P
--   - encoding: Θ_P = {θ : Λ_P(θ) < ∞}; P^z = exp(θ_P(z)x − Λ_P(θ_P(z))) P(dx); I_P the means of these laws; d_P the KL divergence (3) → natParamSet P = {θ : x ↦ e^{θx} is P-integrable}; tilt = Measure.tilted; meanSet P requires a finite mean; θ_P(z) a choice of θ with mean z; dP = klDiv in ℝ≥0∞; reason: same sets and laws (Λ_P(θ) < ∞ iff e^{θx} is integrable; θ_P(z) is unique unless P is a point mass, where every tilt is P); avoids the junk value 0 of Mathlib's cgf at non-integrable θ
--   - encoding: P_νπ on ([K] × ℝ)^∞ (p. 7), events about N_i(T) → banditMeasure ν π T on the histories of the first T rounds (published BanditPolicy), N_i(T) = armPullCount i h; reason: the infinite-horizon law restricted to the first T rounds is exactly banditMeasure ν π T, and N_i(T) depends only on those rounds
-- source:
--   Fan, Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p. 38, Appendix A, (47); p. 39 (case i ≥ 3)

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

namespace FragileBandit.CauchyTail

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- (47) (Appendix A, p. 38, for the second-best arm; p. 39 for the `i`-th-best arm, `i ≥ 3`), posed for
every arm `k`: for an `M_P`-optimized `π`, `ν ∈ M_P^K` with distinct means and `γ ∈ (0, 1)`,
`liminf_T log P_νπ(N_k(T) > (1−γ)T) / log T ≥ −∑_{j : µ_j > µ_k} inf_{z ∈ I_P, z < µ_k} d_P(z, µ_j)/d_P(z, µ_k)`,
in power form: for every `a` above the exponent, eventually `P_νπ(N_k(T) > (1−γ)T) ≥ T^{−a}`. -/
theorem eq_47 {K : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (π : BanditPolicy K) (hπ : IsOptimized P π)
    (ν : StochasticBandit K) (hν : IsModelEnv P ν) (hd : DistinctMeans ν) (k : Fin K)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ a : ℝ, tailExponent P ν k < ENNReal.ofReal a → ∀ᶠ T : ℕ in atTop,
      ENNReal.ofReal ((T : ℝ) ^ (-a)) ≤
        banditMeasure ν π T {h | (1 - γ) * (T : ℝ) < (armPullCount k h : ℝ)} := by sorry

end FragileBandit.CauchyTail
