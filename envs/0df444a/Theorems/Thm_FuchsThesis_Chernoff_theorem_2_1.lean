-- Prove2me | Theorems.Thm_FuchsThesis_Chernoff_theorem_2_1
-- name    : FuchsThesis.Chernoff.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:16.223624+00:00
-- url     : https://prove2.me/theorems/2022806f-aead-447a-bc39-b809014b8579
-- title:
--   Theorem 2.1 (Chernoff) (corrected: positive priors for the asymptotic clause)
-- statement:
--   Let $p_0, p_1$ be probability distributions on a finite outcome set $\{1,\dots,n\}$, and let $\pi_0, \pi_1 \ge 0$ with $\pi_0 + \pi_1 = 1$ be the prior probabilities of the two hypotheses. Let $P_e(N)$ be the probability of error for Bayes' decision rule after sampling $N$ times one of the two distributions. Define
--
--   $$
--   \lambda = \inf_{0 \le \alpha \le 1} F_\alpha(p_0/p_1), \qquad F_\alpha(p_0/p_1) = \sum_{b=1}^{n} p_0(b)^{\alpha} p_1(b)^{1-\alpha}.
--   $$
--
--   Then:
--
--   1. for every $N \ge 0$,
--   $$
--   P_e(N) \le \lambda^{N};
--   $$
--   2. if moreover $\pi_0 > 0$ and $\pi_1 > 0$, the bound is approached asymptotically:
--   $$
--   \lim_{N\to\infty} P_e(N)^{1/N} = \lambda.
--   $$
--
--   The constant $\lambda$ depends neither on the priors nor on the number of samples, which makes it a distinguishability measure for probability distributions that adapts to repeated sampling, unlike the one-sample Bayes error.
--
--   **Formalization Note** $P_e(N)$ is the sum over strings of length $N$ of $\min\{\pi_0 p_0, \pi_1 p_1\}$ for the product distributions; the milestones (2.9) and (2.11) identify it with the error of Bayes' decision rule. Real powers use $0^0 = 1$, and $P_e(N)^{1/N}$ is a real power with exponent $1/N$ (exponent $0$ at $N = 0$, which does not affect the limit).
--
--   Differences from the source:
--   - reading: λ = min over α ∈ [0, 1] of Fα → λ = inf over α ∈ [0, 1] of Fα; reason: with real powers and 0^0 = 1 the minimum need not be attained (p0 = (1, 0), p1 = (½, ½): Fα = 2^{α−1} for α > 0, F0 = 1); the infimum is the Chernoff constant, the value of the minimum of the continuous extension of α ↦ Fα
--   - reading: "this bound is approached asymptotically in the limit of large N" → lim_{N→∞} Pe(N)^{1/N} = λ; reason: the exponential-rate reading of the surrounding text ("the decrease asymptotically approaches an exponential"); the literal Pe(N)/λ^N → 1 is false (p0 = (¼, ¾), p1 = (¾, ¼), π0 = π1 = ½: λ = √3/2 and Pe(N)/λ^N ≈ 0.206, 0.077, 0.025 at N = 10, 100, 1000)
--   - correction: asymptotic clause for all priors → asymptotic clause under π0 > 0 and π1 > 0; reason: counterexample π0 = 0, π1 = 1, p0 = p1 = (½, ½): Pe(N) = 0 for every N while λ = 1; the bound Pe(N) ≤ λ^N is kept for all priors
--   - encoding: outcome set {1, …, n} → arbitrary finite type B; reason: every finite set is in bijection with some {1, …, n}, and IsDist forces it to be nonempty; no instance changes
--   - encoding: strings b1…bN with trials k = 1, …, N → functions s : Fin N → B with trials indexed from 0; reason: the same finite set of strings; no instance changes
--   - encoding: Pe(N), the probability of error for Bayes' decision rule after N samplings → errorProbN := ∑ over s : Fin N → B of min{π0 ∏ p0(s k), π1 ∏ p1(s k)}; reason: this is (2.11) on B^N and the first line of (2.28) with the misprints of (2.21) and (2.28) not copied; (2.9) and (2.11) identify it with the error of Bayes' rule
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.1, eqs. (2.18)–(2.20), p.16 (PDF p.25)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_FuchsThesis_Chernoff_errorProbN
import Definitions.Def_FuchsThesis_Chernoff_chernoffConst

open CalibratedCE.Forecast Filter Topology

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.1 (Chernoff), eqs. (2.18)–(2.20), p.16 (PDF p.25).

Let `Pe(N)` be the probability of error for Bayes' decision rule after sampling `N` times one of
the two distributions `p0`, `p1` (priors `π0, π1 ≥ 0`, `π0 + π1 = 1`). Then `Pe(N) ≤ λ^N` (2.18)
with `λ = min_{α ∈ [0,1]} Fα(p0/p1)` (2.19), `Fα(p0/p1) = ∑_b p0(b)^α p1(b)^{1−α}` (2.20).
Moreover this bound is approached asymptotically in the limit of large `N`.

**Formalization Note.**
* `λ` is the infimum over `α ∈ [0, 1]` (`chernoffConst`); with `Real.rpow`'s `0 ^ 0 = 1` the
  minimum need not be attained.
* "Approached asymptotically" is read as the exponential rate: `Pe(N)^{1/N} → λ`. (The literal
  `Pe(N)/λ^N → 1` is false: `p0 = (¼, ¾)`, `p1 = (¾, ¼)`, equal priors.)
* The asymptotic clause is stated under `π0 > 0` and `π1 > 0`, which the source omits: for
  `π0 = 0`, `π1 = 1`, `p0 = p1 = (½, ½)` one has `Pe(N) = 0` for all `N` while `λ = 1`.
* `Pe(N)^{1/N}` is `Real.rpow` with exponent `1 / N` (at `N = 0` the exponent is `0`, which does
  not affect the limit). -/
theorem theorem_2_1 {B : Type} [Fintype B] (π0 π1 : ℝ) (p0 p1 : B → ℝ)
    (hp0 : IsDist p0) (hp1 : IsDist p1) (hπ0 : 0 ≤ π0) (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1) :
    (∀ N : ℕ, errorProbN π0 π1 p0 p1 N ≤ chernoffConst p0 p1 ^ N) ∧
      (0 < π0 → 0 < π1 →
        Tendsto (fun N : ℕ => errorProbN π0 π1 p0 p1 N ^ (1 / (N : ℝ))) atTop
          (𝓝 (chernoffConst p0 p1))) := by sorry

end FuchsThesis.Chernoff
