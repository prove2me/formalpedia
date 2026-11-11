-- Prove2me | Theorems.Thm_GMMIsoSample_Main_theorem_2
-- name    : GMMIsoSample.Main.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:32:07.255566+00:00
-- url     : https://prove2.me/theorems/0176c3f8-c11d-40b2-9d40-f2d6b24002dc
-- title:
--   Theorem 2 — sharp sample complexity of density estimation up to isometry for every separation regime
-- statement:
--   A target is a mixture $D$ of $k\le k_{\max}$ spherical Gaussians $N(\mu_i,\sigma_i^2I_d)$ on $\mathbb R^d$ with mixing weights $w_i\ge w_{\min}$ and normalized minimum separation $\Gamma(D)=\min_{i<j}\|\mu_i-\mu_j\|/\sqrt{\sigma_i^2+\sigma_j^2}\ge\Gamma_{\min}$. An $\varepsilon$-density estimator up to isometry with $T$ samples receives $T$ i.i.d. points from an unknown target and, with probability at least $9/10$, outputs a mixture of at most $k_{\max}$ spherical Gaussians that is within total variation $\varepsilon$ of the target after some Euclidean isometry; $N_{k_{\max}}(d,\Gamma_{\min},\varepsilon,w_{\min})$ is the least such $T$. Fix $0<\varepsilon\le1/100$. Then for sufficiently large $d$:
--
--   (a) for $k_{\max}=2$ and $0<w_{\min}\le1/2$,
--   $$N_2(d,\Gamma_{\min},\varepsilon,w_{\min})=\tilde\Theta\Big(\min\Big\{d,\;1+\frac d{\Gamma_{\min}^4}+\frac{\sqrt d}{\Gamma_{\min}}\Big\}\Big);$$
--   (b) for $k_{\max}>2$ and $0<w_{\min}\le1/3$, $N_{k_{\max}}(d,\Gamma_{\min},\varepsilon,w_{\min})=\tilde\Theta(\min\{d,\,d/\Gamma_{\min}^4+\sqrt d\})$.
--
--   Here $\tilde\Theta$ hides polylogarithmic factors in $d$ and constants depending on $\varepsilon,k_{\max},w_{\min}$, uniformly in $\Gamma_{\min}>0$: there are $c,C>0$, $a\ge0$, $d_0$ such that for $d\ge d_0$ and every $\Gamma_{\min}>0$ some estimator uses at most $C(\log d)^af$ samples, and every estimator uses at least $cf/(\log d)^a$. In particular $o(d)$ samples suffice once $\Gamma_{\min}\ge\mathrm{polylog}(d)$.
--
--   Differences from the source:
--
--   - reading: N = Θ̃(f) with Θ̃ suppressing polylog(d) factors and constants depending on ε, kmax, wmin, for sufficiently large d → ∃ c, C > 0, a ≥ 0, d₀ (depending on ε, kmax, wmin) such that for all d ≥ d₀ and every Γmin > 0: an estimator with T ≤ C (log d)^a f exists, and every estimator has T ≥ c f/(log d)^a; reason: the paper's description of Θ̃ (p. 3); the bounds are uniform in Γmin, which is not a constant
--   - encoding: the sample complexity N_kmax (a least sample size) → the upper half as existence of a successful estimator with T samples, the lower half as a bound on T for every successful estimator; reason: equivalent to the two-sided bound on the minimum, without a junk infimum of a possibly empty set
--   - encoding: output k̂ with 1 ≤ k̂ ≤ kmax and parameters (ŵ_i, σ̂_i, μ̂_i)_{i ≤ k̂} → a kmax-slot parameter tuple with nonnegative weights summing to 1 and positive radii (unused slots have weight 0); reason: the same set of hypothesis distributions; positivity of σ̂ and ŵ being a probability vector are what 'mixing weights' and 'radii' mean
--   - encoding: a randomized algorithm (estimator / distinguisher) using T sample points → a Markov kernel from (ℝ^d)^T to its outputs; reason: the kernel is the law of the output given the sample, i.e. the algorithm's internal randomness; the success probability is the joint law of samples and randomness
--   - encoding: target D = Mix(μ̄, σ̄, w̄), components indexed by [k] → a parameter tuple p : Fin k → ℝ × ℝ × ℝ^d (0-based) with mix p = Σ w_i N(μ_i, σ_i² I_d); reason: the paper itself parametrizes targets by these tuples; Γ(D) ≥ Γ is the pairwise condition over i ≠ j
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 3, Theorem 2

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Theorem 2 (p. 3): for every `0 < ε ≤ 1/100` the sample complexity of `ε`-density estimation
up to isometry is `Θ̃(f(d, Γmin))` for all sufficiently large `d`, uniformly in `Γmin > 0`, with
(a) `f = min{d, 1 + d/Γmin⁴ + √d/Γmin}` for `kmax = 2`, `0 < wmin ≤ 1/2`, and
(b) `f = min{d, d/Γmin⁴ + √d}` for `kmax > 2`, `0 < wmin ≤ 1/3`.
`Θ̃` is read as: there are `c, C > 0`, `a ≥ 0` and `d₀` (depending only on `ε`, `kmax`, `wmin`)
such that for every `d ≥ d₀` and every `Γmin > 0`, some estimator using at most
`C (log d)^a f` samples succeeds on the whole class, and every estimator that succeeds with `T`
samples has `T ≥ c f / (log d)^a`. -/
theorem theorem_2 :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ wmin : ℝ, 0 < wmin → wmin ≤ 1 / 2 →
      ∃ c C a : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ a ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ∀ Γmin : ℝ, 0 < Γmin →
          (∃ T : ℕ, (T : ℝ) ≤ C * Real.log d ^ a * rateTwo d Γmin ∧
            ∃ K : Kernel (Fin T → E d) (Params d 2), IsEstimator d 2 wmin Γmin ε T K) ∧
          (∀ (T : ℕ) (K : Kernel (Fin T → E d) (Params d 2)),
            IsEstimator d 2 wmin Γmin ε T K → c * rateTwo d Γmin / Real.log d ^ a ≤ T)) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ kmax : ℕ, 2 < kmax →
      ∀ wmin : ℝ, 0 < wmin → wmin ≤ 1 / 3 →
      ∃ c C a : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ a ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ∀ Γmin : ℝ, 0 < Γmin →
          (∃ T : ℕ, (T : ℝ) ≤ C * Real.log d ^ a * rateMany d Γmin ∧
            ∃ K : Kernel (Fin T → E d) (Params d kmax), IsEstimator d kmax wmin Γmin ε T K) ∧
          (∀ (T : ℕ) (K : Kernel (Fin T → E d) (Params d kmax)),
            IsEstimator d kmax wmin Γmin ε T K → c * rateMany d Γmin / Real.log d ^ a ≤ T)) := by sorry

end GMMIsoSample.Main
