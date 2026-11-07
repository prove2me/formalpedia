-- Prove2me | Theorems.Thm_GaussMixHH_theorem_1
-- name    : GaussMixHH.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:01.369198+00:00
-- url     : https://prove2.me/theorems/fd3029bc-24ca-4deb-973c-83f6e03b2f96
-- title:
--   Theorem 1, p.4 — solving (EP) for separated homogeneous Gaussian mixtures with $\exp(O(\log^{4/3}(1/\varepsilon_{wt})\,n^{1/3}/\varepsilon_{dist}^{4/3}))$ samples and time
-- statement:
--   Let $D$ be a probability distribution on $\mathbb R^n$ supported on a set $\mathrm{Supp}$ of centers, finite or infinite, any two of which are at distance at least $\Delta_{\min}$, and let $D'=\mathrm{Mix}(D,1)=D*N(0,I_n)$.
--
--   There are one program $P$ of the sampling real RAM, a constant $C>0$ and a threshold $n_0(\varepsilon_{wt},\varepsilon_{dist})$ such that the following holds. Let $0<\varepsilon_{wt}\le1/8$, $0<\varepsilon_{dist}\le1$ with $\varepsilon_{dist}<\Delta_{\min}/2$, $n\ge n_0(\varepsilon_{wt},\varepsilon_{dist})$, $D$ as above and $z\in\mathbb R^n$. Run $P$ on input $(n;\varepsilon_{wt},\varepsilon_{dist},\Delta_{\min},z)$ with fair coins and i.i.d. samples from $D'$, and put
--
--   $$T=\exp\Big(C\,\frac{\log^{4/3}(1/\varepsilon_{wt})}{\varepsilon_{dist}^{4/3}}\,n^{1/3}\Big).$$
--
--   1. On every coin tape and sample stream, $P$ halts within at most $T$ steps and uses at most $T$ samples.
--   2. *(Soundness.)* If no center lies within $\varepsilon_{dist}$ of $z$, then with probability at least $9/10$ the output is $\hat w=0$.
--   3. *(Completeness.)* If $\|\mu-z\|\le\varepsilon_{dist}/2$ for some center $\mu$, then with probability at least $9/10$, $|\hat w-D(\mu)|\le\varepsilon_{wt}$.
--
--   The bound does not depend on the number of centers, and the paper's Theorem 2 shows that its sample complexity is essentially optimal.
--
--   **Formalization Note** The machine is `GaussMixHH.Machine`; the program sees $D$ only through the `sample` instruction. Supp is the set of positive-weight atoms of $D$, which is required to be purely atomic.
--
--   Differences from the source:
--   - reading: "there is an algorithm", running time in "the real arithmetic model" (p.15) → one Admissible program of GaussMixHH.Machine (rational literals, pointer-to-real cast, √, exp, cos, sin, fair coins, sample of cost n, halt) for all inputs; reason: the paper names no instruction set; this is the weakest model its runtime count (p.28) uses, and n, εwt, εdist, ∆min, z are inputs
--   - encoding: exp(O(log^{4/3}(1/εwt)/εdist^{4/3} · n^{1/3})) and "n sufficiently large in terms of εwt and εdist" → ∃ C > 0 and n₀ : ℝ → ℝ → ℕ chosen with P before all parameters; T = exp(C·log(1/εwt)^{4/3}·n^{1/3}/εdist^{4/3}); reason: the meaning of O(·) and of the threshold; log(1/εwt) ≥ log 8 > 0
--   - reading: sample complexity and running time "at most" → worst-case bounds on every coin tape and sample stream; reason: the proof's sample sizes and iteration counts are deterministic
--   - reading: randomness of the algorithm → a tape of fair coins (no uniform-real draws); reason: a uniform-real machine simulates coins, so this is the stronger form
--   - encoding: "with probability at least 9/10", i.i.d. samples from D′ → ∃ measurable E with 9/10 ≤ P(E) under fair coins × i.i.d. D ∗ N(0, I_n), separately under each promise; reason: the promises exclude each other; avoids outer measure
--   - reading: Supp and D(μ) of a discrete D (finite or infinite) → D purely atomic, Supp = its positive-weight atoms, D(μ) = D{μ}; reason: makes the separation hypothesis and the soundness promise as weak as possible
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 1, p.4 (PDF p.6), restated p.18; model and Separation Assumption p.2, (EP) p.4; proof pp.28–29

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussMixHH_CenterModel

open MeasureTheory ProbabilityTheory

namespace GaussMixHH

/-- **Theorem 1** (An estimation algorithm for mixtures of homogeneous spherical Gaussians).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 1, p.4 (PDF p.6), restated
p.18; the model and the Separation Assumption are on p.2, (EP) on p.4.

"Let 0 < εwt ≤ 1/8 and 0 < εdist ≤ 1, with εdist < ∆min/2. For n sufficiently large in terms of εwt
and εdist, there is an algorithm Estimator(εwt, εdist, ∆min, z) that solves (EP) for mixtures of
identity covariance Gaussians over Rn with probability at least 9/10. Its sample complexity and
running time are at most exp(O(log^{4/3}(1/εwt)/εdist^{4/3} · n^{1/3}))."

(EP): "(Soundness) If no center μ ∈ Supp lies within εdist of z, then ŵ = 0. (Completeness) If
∥μ − z∥ ≤ εdist/2 for some μ ∈ Supp (which must be unique), then |ŵ − D(μ)| ≤ εwt."

**Formalization Note.**
* The machine is `GaussMixHH.Machine`, a reading of "the real arithmetic model" (p.15): the
  published real-RAM core with rational literals, a pointer-to-real cast, `√`, `exp`, `cos`, `sin`,
  fair coins, `sample` (cost `n`) and `halt`. One `Admissible` program `P` serves every input; it
  receives `n` in pointer `0` and `εwt, εdist, ∆min, z` in memory (`goalInput`), and outputs
  `ŵ = r[0]`. It sees `D` only through `sample`.
* `O(·)` and "n sufficiently large in terms of εwt and εdist": `∃ C > 0` and `∃ n₀(εwt, εdist)`,
  chosen with `P` before all parameters; the bound is
  `T = exp(C · log(1/εwt)^{4/3} · n^{1/3} / εdist^{4/3})` (`Real.rpow`; `log(1/εwt) ≥ log 8 > 0`).
* `T` bounds the work and the number of samples on every coin tape and sample stream.
* Randomness: `sampleSpace D` = fair coin tape × i.i.d. samples of `Mix(D, 1) = D ∗ N(0, I_n)`.
  Each guarantee holds on a measurable set of probability at least `9/10`, under its own promise
  (the promises exclude each other).
* `D` is a probability measure on `ℝⁿ`, purely atomic with positive-weight atoms `Supp D` pairwise
  `∆min`-separated (`IsSeparatedAtomic`); `Supp D` may be infinite. `D(μ)` is `D{μ}`. -/
theorem theorem_1 :
    ∃ (P : Program) (_ : Admissible P) (C : ℝ) (n₀ : ℝ → ℝ → ℕ), 0 < C ∧
      ∀ (εwt εdist Δmin : ℝ), 0 < εwt → εwt ≤ 1 / 8 → 0 < εdist → εdist ≤ 1 → 2 * εdist < Δmin →
      ∀ n : ℕ, n₀ εwt εdist ≤ n →
      ∀ (D : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure D],
        IsSeparatedAtomic Δmin D →
      ∀ z : EuclideanSpace ℝ (Fin n),
        let T := Real.exp (C * Real.log (1 / εwt) ^ ((4 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 3) /
          εdist ^ ((4 : ℝ) / 3))
        (∀ ω, ∃ t, (run P n (goalInput n εwt εdist Δmin z) ω t).halted = true ∧
          ((run P n (goalInput n εwt εdist Δmin z) ω t).work : ℝ) ≤ T ∧
          ((run P n (goalInput n εwt εdist Δmin z) ω t).samplesUsed : ℝ) ≤ T) ∧
        ((∀ μ ∈ Supp D, εdist < dist μ z) →
          ∃ E, MeasurableSet E ∧ 9 / 10 ≤ (sampleSpace D E).toReal ∧
            ∀ ω ∈ E, ∀ t, (run P n (goalInput n εwt εdist Δmin z) ω t).halted = true →
              output (run P n (goalInput n εwt εdist Δmin z) ω t) = 0) ∧
        (∀ μ ∈ Supp D, dist μ z ≤ εdist / 2 →
          ∃ E, MeasurableSet E ∧ 9 / 10 ≤ (sampleSpace D E).toReal ∧
            ∀ ω ∈ E, ∀ t, (run P n (goalInput n εwt εdist Δmin z) ω t).halted = true →
              |output (run P n (goalInput n εwt εdist Δmin z) ω t) - (D {μ}).toReal| ≤ εwt) := by sorry

end GaussMixHH
