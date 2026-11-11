-- Prove2me | Theorems.Thm_GMMIsoSample_Main_proposition_10
-- name    : GMMIsoSample.Main.proposition_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:32:12.586384+00:00
-- url     : https://prove2.me/theorems/68adeea8-2403-42fd-8185-971490bb2513
-- title:
--   Proposition 10 — the upper bounds part of Theorem 2
-- statement:
--   Fix $0<\varepsilon\le1/100$. (a) For $k_{\max}=2$ and $0<w_{\min}\le1/2$,
--   $$N_2(d,\Gamma_{\min},\varepsilon,w_{\min})\le\tilde O_{\varepsilon,w_{\min}}\Big(\min\Big\{d,1+\frac d{\Gamma_{\min}^4}+\frac{\sqrt d}{\Gamma_{\min}}\Big\}\Big);$$
--   (b) for $k_{\max}>2$ and $0<w_{\min}\le1/3$, $N_{k_{\max}}(d,\Gamma_{\min},\varepsilon,w_{\min})\le\tilde O_{\varepsilon,k_{\max},w_{\min}}(\min\{d,d/\Gamma_{\min}^4+\sqrt d\})$. Concretely: there are $C>0$, $a\ge0$ and $d_0$ depending only on the subscript parameters such that for every $d\ge d_0$ and every $\Gamma_{\min}>0$ some randomized estimator using $T\le C(\log d)^af(d,\Gamma_{\min})$ sample points $\varepsilon$-estimates every target of the class up to isometry with probability at least $9/10$.
--
--   This is the algorithmic half of the main result.
--
--   Differences from the source:
--
--   - reading: N_kmax ≤ Õ_{subscript}(f), for sufficiently large d → ∃ C > 0, a ≥ 0, d₀ (depending on the subscript parameters) such that for all d ≥ d₀ and Γmin > 0 some estimator with T ≤ C (log d)^a f succeeds; reason: Õ suppresses polylog(d) factors and constants depending on the subscript (p. 15); stating existence of the estimator avoids a junk infimum
--   - encoding: output k̂ with 1 ≤ k̂ ≤ kmax and parameters (ŵ_i, σ̂_i, μ̂_i)_{i ≤ k̂} → a kmax-slot parameter tuple with nonnegative weights summing to 1 and positive radii (unused slots have weight 0); reason: the same set of hypothesis distributions; positivity of σ̂ and ŵ being a probability vector are what 'mixing weights' and 'radii' mean
--   - encoding: a randomized algorithm (estimator / distinguisher) using T sample points → a Markov kernel from (ℝ^d)^T to its outputs; reason: the kernel is the law of the output given the sample, i.e. the algorithm's internal randomness; the success probability is the joint law of samples and randomness
--   - encoding: target D = Mix(μ̄, σ̄, w̄), components indexed by [k] → a parameter tuple p : Fin k → ℝ × ℝ × ℝ^d (0-based) with mix p = Σ w_i N(μ_i, σ_i² I_d); reason: the paper itself parametrizes targets by these tuples; Γ(D) ≥ Γ is the pairwise condition over i ≠ j
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), pp. 14–15, Proposition 10

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Proposition 10 (pp. 14–15), the upper bounds part of Theorem 2: for every `0 < ε ≤ 1/100`,
(a) for `kmax = 2`, `0 < wmin ≤ 1/2`: `N₂(d, Γmin, ε, wmin) ≤ Õ_{ε,wmin}(min{d, 1 + d/Γmin⁴ +
√d/Γmin})`; (b) for `kmax > 2`, `0 < wmin ≤ 1/3`: `N_kmax ≤ Õ_{ε,kmax,wmin}(min{d, d/Γmin⁴ + √d})`.
`Õ` is read as: there are `C > 0`, `a ≥ 0` and `d₀` (depending only on the subscript
parameters) such that for every `d ≥ d₀` and `Γmin > 0` some estimator using at most
`C (log d)^a f` samples succeeds on the whole class. -/
theorem proposition_10 :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ wmin : ℝ, 0 < wmin → wmin ≤ 1 / 2 →
      ∃ C a : ℝ, 0 < C ∧ 0 ≤ a ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ Γmin : ℝ, 0 < Γmin →
        ∃ T : ℕ, (T : ℝ) ≤ C * Real.log d ^ a * rateTwo d Γmin ∧
          ∃ K : Kernel (Fin T → E d) (Params d 2), IsEstimator d 2 wmin Γmin ε T K) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ kmax : ℕ, 2 < kmax →
      ∀ wmin : ℝ, 0 < wmin → wmin ≤ 1 / 3 →
      ∃ C a : ℝ, 0 < C ∧ 0 ≤ a ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ Γmin : ℝ, 0 < Γmin →
        ∃ T : ℕ, (T : ℝ) ≤ C * Real.log d ^ a * rateMany d Γmin ∧
          ∃ K : Kernel (Fin T → E d) (Params d kmax), IsEstimator d kmax wmin Γmin ε T K) := by sorry

end GMMIsoSample.Main
