-- Prove2me | Theorems.Thm_GMMIsoSample_Main_proposition_54
-- name    : GMMIsoSample.Main.proposition_54
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:32:31.592931+00:00
-- url     : https://prove2.me/theorems/4bd334f2-2e30-48cb-b9eb-4630572ce057
-- title:
--   Proposition 54 — kmax = 2: Ω(√d/Γmin) samples are necessary for Γmin ≥ 16√2
-- statement:
--   There is an absolute constant $c>0$ such that for all sufficiently large $d$, every $\Gamma_{\min}\ge16\sqrt2$, every $0<w_{\min}\le1/2$ and every $0<\varepsilon\le1/100$: every randomized estimator that $\varepsilon$-estimates up to isometry, with probability at least $9/10$, every equal-weight, unit-radius target with at most $2$ components and $\Gamma(D)\ge\Gamma_{\min}$ uses
--   $$T\ge c\,\frac{\sqrt d}{\Gamma_{\min}}$$
--   sample points. It is the $\sqrt d/\Gamma_{\min}$ term of the lower bound in Theorem 2(a).
--
--   Differences from the source:
--
--   - reading: Ω(√d/Γmin), for sufficiently large d → ∃ c > 0 (and d₀) chosen before Γmin, wmin and ε; reason: Ω hides an absolute constant (the proofs give explicit ones); §9 fixes any 0 < ε ≤ 1/100
--   - reading: '(even for equal-weight, unit-radius mixture distributions)' → the estimator is only required to succeed on the equal-weight, unit-radius targets of the class (IsEstimatorEqualUnit); reason: the stronger of the two readings, and the one the parenthesis asserts; it implies the bound for all estimators of the class
--   - encoding: output k̂ with 1 ≤ k̂ ≤ kmax and parameters (ŵ_i, σ̂_i, μ̂_i)_{i ≤ k̂} → a kmax-slot parameter tuple with nonnegative weights summing to 1 and positive radii (unused slots have weight 0); reason: the same set of hypothesis distributions; positivity of σ̂ and ŵ being a probability vector are what 'mixing weights' and 'radii' mean
--   - encoding: a randomized algorithm (estimator / distinguisher) using T sample points → a Markov kernel from (ℝ^d)^T to its outputs; reason: the kernel is the law of the output given the sample, i.e. the algorithm's internal randomness; the success probability is the joint law of samples and randomness
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 70, Proposition 54

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Proposition 54 (p. 70): for sufficiently large `d` and `Γmin ≥ 16√2`, `ε`-density estimation
up to isometry when `kmax = 2` requires `Ω(√d/Γmin)` sample points, even for equal-weight,
unit-radius mixtures. `Ω` is read as an absolute constant `c > 0` (and `d₀`), uniform in `Γmin`,
`wmin ≤ 1/2` and `ε ≤ 1/100`. -/
theorem proposition_54 :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ Γmin : ℝ, 16 * Real.sqrt 2 ≤ Γmin →
      ∀ wmin : ℝ, 0 < wmin → wmin ≤ 1 / 2 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 →
        ∀ (T : ℕ) (K : Kernel (Fin T → E d) (Params d 2)),
          IsEstimatorEqualUnit d 2 wmin Γmin ε T K → c * Real.sqrt d / Γmin ≤ T := by sorry

end GMMIsoSample.Main
