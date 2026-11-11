-- Prove2me | Theorems.Thm_GMMIsoSample_Main_proposition_53
-- name    : GMMIsoSample.Main.proposition_53
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:32:26.462729+00:00
-- url     : https://prove2.me/theorems/4e2d58c2-b2f6-4ec7-889c-9b34e812ec82
-- title:
--   Proposition 53 — kmax = 2: Ω(d/Γmin⁴) samples are necessary for Γmin ≥ 8
-- statement:
--   There is an absolute constant $c>0$ such that for all sufficiently large $d$, every $\Gamma_{\min}\ge8$, every $0<w_{\min}\le1/2$ and every $0<\varepsilon\le1/100$: every randomized estimator that $\varepsilon$-estimates up to isometry, with probability at least $9/10$, every equal-weight, unit-radius target with at most $k_{\max}=2$ components and $\Gamma(D)\ge\Gamma_{\min}$ uses
--   $$T\ge c\,\frac d{\Gamma_{\min}^4}$$
--   sample points. It is the $d/\Gamma_{\min}^4$ term of the lower bound in Theorem 2.
--
--   Differences from the source:
--
--   - reading: Ω(d/Γmin⁴), for sufficiently large d → ∃ c > 0 (and d₀) chosen before Γmin, wmin and ε; reason: Ω hides an absolute constant (the proofs give explicit ones); §9 fixes any 0 < ε ≤ 1/100
--   - reading: '(even for equal-weight, unit-radius mixture distributions)' → the estimator is only required to succeed on the equal-weight, unit-radius targets of the class (IsEstimatorEqualUnit); reason: the stronger of the two readings, and the one the parenthesis asserts; it implies the bound for all estimators of the class
--   - encoding: output k̂ with 1 ≤ k̂ ≤ kmax and parameters (ŵ_i, σ̂_i, μ̂_i)_{i ≤ k̂} → a kmax-slot parameter tuple with nonnegative weights summing to 1 and positive radii (unused slots have weight 0); reason: the same set of hypothesis distributions; positivity of σ̂ and ŵ being a probability vector are what 'mixing weights' and 'radii' mean
--   - encoding: a randomized algorithm (estimator / distinguisher) using T sample points → a Markov kernel from (ℝ^d)^T to its outputs; reason: the kernel is the law of the output given the sample, i.e. the algorithm's internal randomness; the success probability is the joint law of samples and randomness
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 69, Proposition 53

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Proposition 53 (p. 69): for sufficiently large `d` and `Γmin ≥ 8`, `ε`-density estimation up
to isometry when `kmax = 2` requires `Ω(d/Γmin⁴)` sample points, even for equal-weight, unit-radius
mixtures. `Ω` is read as an absolute constant `c > 0` (and `d₀`), uniform in `Γmin`, `wmin ≤ 1/2`
and `ε ≤ 1/100`; the estimator need only succeed on the equal-weight unit-radius targets. -/
theorem proposition_53 :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ Γmin : ℝ, 8 ≤ Γmin →
      ∀ wmin : ℝ, 0 < wmin → wmin ≤ 1 / 2 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 →
        ∀ (T : ℕ) (K : Kernel (Fin T → E d) (Params d 2)),
          IsEstimatorEqualUnit d 2 wmin Γmin ε T K → c * d / Γmin ^ 4 ≤ T := by sorry

end GMMIsoSample.Main
