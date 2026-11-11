-- Prove2me | Theorems.Thm_GMMIsoSample_Main_proposition_57
-- name    : GMMIsoSample.Main.proposition_57
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:32:21.703868+00:00
-- url     : https://prove2.me/theorems/b9917b80-4b4f-44ea-a039-f8fef336bd54
-- title:
--   Proposition 57 — kmax ≥ 3: Ω(√d) samples are necessary for Γmin > 160
-- statement:
--   There is an absolute constant $c>0$ such that for every $d\ge2$, every $\Gamma_{\min}>160$, every $k_{\max}\ge3$, every $0<w_{\min}\le1/3$ and every $0<\varepsilon\le1/100$: every randomized estimator that $\varepsilon$-estimates up to isometry, with probability at least $9/10$, every equal-weight, unit-radius target with at most $k_{\max}$ components and $\Gamma(D)\ge\Gamma_{\min}$ uses
--   $$T\ge c\sqrt d$$
--   sample points. It is the $\sqrt d$ term of the lower bound in Theorem 2(b).
--
--   Differences from the source:
--
--   - reading: Ω(√d) → ∃ c > 0 chosen before d, Γmin, kmax, wmin and ε; reason: Ω hides an absolute constant; the statement is for every d ≥ 2
--   - reading: '(even for equal-weight, unit-radius mixture distributions)' → the estimator is only required to succeed on the equal-weight, unit-radius targets of the class (IsEstimatorEqualUnit); reason: the stronger of the two readings, and the one the parenthesis asserts; it implies the bound for all estimators of the class
--   - encoding: output k̂ with 1 ≤ k̂ ≤ kmax and parameters (ŵ_i, σ̂_i, μ̂_i)_{i ≤ k̂} → a kmax-slot parameter tuple with nonnegative weights summing to 1 and positive radii (unused slots have weight 0); reason: the same set of hypothesis distributions; positivity of σ̂ and ŵ being a probability vector are what 'mixing weights' and 'radii' mean
--   - encoding: a randomized algorithm (estimator / distinguisher) using T sample points → a Markov kernel from (ℝ^d)^T to its outputs; reason: the kernel is the law of the output given the sample, i.e. the algorithm's internal randomness; the success probability is the joint law of samples and randomness
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 71, Proposition 57

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Proposition 57 (p. 71): for every `d ≥ 2` and every `Γmin > 160`, `ε`-density estimation up to
isometry when `kmax ≥ 3` and `wmin ∈ (0, 1/3]` requires `Ω(√d)` sample points, even for
equal-weight, unit-radius mixtures. `Ω` is read as an absolute constant `c > 0`, uniform in `d`,
`Γmin`, `kmax`, `wmin` and `ε ≤ 1/100`. -/
theorem proposition_57 :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ Γmin : ℝ, 160 < Γmin → ∀ kmax : ℕ, 3 ≤ kmax →
      ∀ wmin : ℝ, 0 < wmin → wmin ≤ 1 / 3 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 →
        ∀ (T : ℕ) (K : Kernel (Fin T → E d) (Params d kmax)),
          IsEstimatorEqualUnit d kmax wmin Γmin ε T K → c * Real.sqrt d ≤ T := by sorry

end GMMIsoSample.Main
