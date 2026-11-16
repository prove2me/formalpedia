-- Prove2me | Theorems.Thm_GaussMixHH_Supplement_theorem_2
-- name    : GaussMixHH.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:37:03.705178+00:00
-- url     : https://prove2.me/theorems/d3a0cb75-64dd-4e80-a559-e27c7619ce6d
-- title:
--   Theorem 2, p.4 — any algorithm for (EP) needs $\exp(\Omega(\log^{4/3}(1/\varepsilon_{wt})\,n^{1/3}/\Delta_{\min}^{4/3}))$ samples
-- statement:
--   **Homogeneous mixture — estimation lower bound.** Suppose $0<\varepsilon_{wt}\le e^{-4}/2$, $0<\Delta_{\min}\le1$ and $0<\varepsilon_{dist}<\Delta_{\min}/2$. For all sufficiently large $n$ relative to $\varepsilon_{wt}$ and $\Delta_{\min}$, every algorithm that solves the estimation problem (EP) with success probability at least $9/10$ must use
--
--   $$\exp\!\Big(\Omega\Big(\frac{\log^{4/3}(1/\varepsilon_{wt})}{\Delta_{\min}^{4/3}}\cdot n^{1/3}\Big)\Big)$$
--
--   samples in the worst case.
--
--   (EP) is the problem of the mission: the algorithm receives $\varepsilon_{wt},\varepsilon_{dist},\Delta_{\min}$, a query point $z\in\mathbb R^n$ and i.i.d. samples from the mixture $\mathrm{Mix}(\mathcal D,1)=\mathcal D*N(0,I_n)$, where $\mathcal D$ is a probability distribution on $\Delta_{\min}$-separated centers. It must output $\widehat w$ with
--
--   1. (Soundness) if no center of $\mathcal D$ lies within $\varepsilon_{dist}$ of $z$, then $\widehat w=0$;
--   2. (Completeness) if $\|\mu-z\|\le\varepsilon_{dist}/2$ for some center $\mu$, then $|\widehat w-\mathcal D(\mu)|\le\varepsilon_{wt}$,
--
--   each with probability at least $9/10$ under its own promise.
--
--   Together with the mission's goal (Theorem 1), this shows that $\exp(\Theta(\log^{4/3}(1/\varepsilon_{wt})\,n^{1/3}))$ samples is the right order when $\varepsilon_{dist}$ is a constant fraction of $\Delta_{\min}$.
--
--   **Formalization Note** An algorithm with a worst-case budget of $m$ samples is any family of Markov kernels $A_z$, one for each query point $z$, from $m$ samples in $\mathbb R^n$ to a real output; it may depend on all the parameters, and it is not restricted to the real RAM of Theorem 1. Its output law is the $m$-fold product of the mixture pushed through $A_z$. The conclusion is $m\ge\exp(c\log(1/\varepsilon_{wt})^{4/3}n^{1/3}/\Delta_{\min}^{4/3})$ with one absolute $c>0$ and one threshold $n_0(\varepsilon_{wt},\Delta_{\min})$, both chosen before all parameters; the bound is uniform in $\varepsilon_{dist}$.
--
--   Differences from the source:
--   - reading: 0 < εdist < ∆/2 → 0 < εdist and 2 * εdist < Δmin; reason: the statement defines no ∆ other than ∆min; the proof applies Theorem 21 with ∆ = ∆min, and (EP) itself requires εdist < ∆min/2
--   - encoding: any algorithm … must use B samples in the worst case → for every m and every family of Markov kernels A z : (Fin m → ℝⁿ) ⇝ ℝ satisfying (EP), B ≤ m; reason: an algorithm whose number of samples is at most m on every run is such a kernel (pad with unread samples, internal randomness inside the kernel); the class contains every algorithm, so the lower bound is not restricted to a machine model
--   - reading: satisfying the estimation guarantee with success probability at least 9/10 → for every probability measure D with IsSeparatedAtomic Δmin D (Supp possibly infinite) and every z, soundness w.p. ≥ 9/10 under its promise and completeness w.p. ≥ 9/10 under its promise; reason: (EP) on p.4 for the model of p.2, where Supp may be infinite; each guarantee is a per-instance probability, as in the published Theorem 1
--   - encoding: Ω(·); for sufficiently large n relative to εwt and ∆min → ∃ c > 0 and n₀ : ℝ → ℝ → ℕ, chosen before all parameters, with n ≥ n₀ εwt Δmin; reason: Lean rendering of the asymptotic notation; n₀ depends only on εwt and ∆min as printed
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 2, p.4 (PDF p.6), restated p.29 (PDF p.31), proof p.30; (EP) p.4; model p.2

import Mathlib
import Definitions.Def_GaussMixHH_CenterModel

open MeasureTheory ProbabilityTheory

namespace GaussMixHH.Supplement

open GaussMixHH

/-- **Theorem 2** (Homogeneous mixture — estimation lower bound).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 2, p.4 (PDF p.6), restated
p.29 (PDF p.31), proof p.30; (EP) on p.4.

"Suppose 0 < εwt ≤ e^{−4}/2, 0 < ∆min ≤ 1, and 0 < εdist < ∆/2. For sufficiently large n relative
to εwt and ∆min, any algorithm satisfying the estimation guarantee with success probability at least
9/10 must use exp(Ω(log^{4/3}(1/εwt)/∆min^{4/3} · n^{1/3})) samples in the worst case."

**Formalization Note.**
* The `∆` in "εdist < ∆/2" is `∆min` (the page's restatement and proof use `∆min`).
* "Any algorithm" with a worst-case budget of `m` samples is any randomized map from the query
  point and `m` samples to a real output: a family of Markov kernels
  `A z : (Fin m → ℝⁿ) ⇝ ℝ`, one per query point `z`. It may depend on `εwt, εdist, ∆min, n` and
  `m` in any way. Its output law on center distribution `D` and query `z` is
  `(Mix(D, 1)^{⊗m}).bind (A z)`. An algorithm that draws a random number of samples, at most `m`
  on every run, is such a kernel (pad with unused samples). Nothing restricts it to the real-RAM
  model of Theorem 1.
* "Satisfying the estimation guarantee with success probability at least 9/10": for every
  probability measure `D` that is purely atomic with `∆min`-separated atoms (`IsSeparatedAtomic`,
  `Supp D` possibly infinite) and every `z ∈ ℝⁿ`, under the soundness promise the output is `0`
  with probability `≥ 9/10`, and under the completeness promise the output is within `εwt` of
  `D(μ)` with probability `≥ 9/10`.
* `Ω(·)` and "sufficiently large n relative to εwt and ∆min": one absolute `c > 0` and one
  `n₀(εwt, ∆min)`, chosen before all parameters; the bound
  `exp(c · log(1/εwt)^{4/3} · n^{1/3} / ∆min^{4/3})` is uniform in `εdist ∈ (0, ∆min/2)`. -/
theorem theorem_2 :
    ∃ (c : ℝ) (n₀ : ℝ → ℝ → ℕ), 0 < c ∧
      ∀ (εwt Δmin εdist : ℝ), 0 < εwt → εwt ≤ Real.exp (-4) / 2 → 0 < Δmin → Δmin ≤ 1 →
      0 < εdist → 2 * εdist < Δmin →
      ∀ n : ℕ, n₀ εwt Δmin ≤ n →
      ∀ (m : ℕ) (A : EuclideanSpace ℝ (Fin n) → Kernel (Fin m → EuclideanSpace ℝ (Fin n)) ℝ),
        (∀ z, IsMarkovKernel (A z)) →
        (∀ (D : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure D],
          IsSeparatedAtomic Δmin D → ∀ z : EuclideanSpace ℝ (Fin n),
            ((∀ μ ∈ Supp D, εdist < dist μ z) →
              9 / 10 ≤ (((Measure.pi fun _ : Fin m => mixture D).bind (A z)) {0}).toReal) ∧
            (∀ μ ∈ Supp D, dist μ z ≤ εdist / 2 →
              9 / 10 ≤ (((Measure.pi fun _ : Fin m => mixture D).bind (A z))
                {w | |w - (D {μ}).toReal| ≤ εwt}).toReal)) →
        Real.exp (c * Real.log (1 / εwt) ^ ((4 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 3) /
          Δmin ^ ((4 : ℝ) / 3)) ≤ (m : ℝ) := by sorry

end GaussMixHH.Supplement
