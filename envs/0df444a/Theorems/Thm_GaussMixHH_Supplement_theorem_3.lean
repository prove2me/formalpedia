-- Prove2me | Theorems.Thm_GaussMixHH_Supplement_theorem_3
-- name    : GaussMixHH.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:37:38.160318+00:00
-- url     : https://prove2.me/theorems/a7778652-69e3-438e-bfb0-673ac3c2b78a
-- title:
--   Theorem 3, p.5 — telling $N(0,4I_n)$ from a separated unit-variance mixture far from the origin needs $\exp(\Omega(n\log n))$ samples
-- statement:
--   **Heterogeneous mixture — estimation lower bound.** Any algorithm that receives i.i.d. samples from $\mathcal D'=\mathrm{Mix}(\mathcal D,r)$ and correctly distinguishes the following two scenarios with success probability at least $9/10$ must use $\exp(\Omega(n\log n))$ samples:
--
--   1. **First scenario:** $\mathcal D$ is the point mass at $0^n$ and $r(0^n)=4$, so the samples come from $N(0,4I_n)$.
--   2. **Second scenario:** $\mathcal D$ is a discrete, finitely supported distribution putting zero mass on every $z\in\mathbb R^n$ with $\|z\|\le1$; in fact every center $\mu$ of $\mathcal D$ satisfies
--   $$n^{0.49}\le\|\mu\|\le\sqrt{n\log n}.$$
--   Moreover $\mathcal D$ has minimum separation $\Delta_{\min}=1$ and $r(\mu)=1$ for every center, so the samples come from $\mathcal D*N(0,I_n)$.
--
--   Here $\mathrm{Mix}(\mathcal D,r)$ draws $\mu\sim\mathcal D$ and outputs a sample of $N(\mu,r(\mu)I_n)$. The theorem shows that once the common variance of the components is unknown, the estimation problem becomes far harder than in the homogeneous case of Theorems 1 and 2: a single centered Gaussian of variance $4$ and a unit-variance mixture with no center near the origin are super-exponentially close.
--
--   **Formalization Note** An algorithm with a worst-case budget of $m$ samples is any Markov kernel from $m$ samples in $\mathbb R^n$ to $\{\text{true},\text{false}\}$ ("true" = first scenario); it may depend on $n$ and $m$ and is not restricted to a machine model. It must answer "first" with probability $\ge9/10$ on $N(0,4I_n)$ (the image of $N(0,I_n)$ under $x\mapsto2x$) and "second" with probability $\ge9/10$ on $\mathcal D*N(0,I_n)$ for **every** second-scenario $\mathcal D$. The conclusion is $m\ge\exp(c\,n\log n)$ for one $c>0$ and all $n\ge n_0$, with $c,n_0$ chosen before $n$.
--
--   Differences from the source:
--   - encoding: first scenario: D = δ_{0ⁿ}, r(0ⁿ) = 4, sample law Mix(D, r) → (stdGaussian ℝⁿ).map (x ↦ 2 • x), i.e. N(0, 4Iₙ); reason: Mix(δ₀, r) with r(0) = 4 is N(0, 4Iₙ), and 2Z ∼ N(0, 4Iₙ) for Z ∼ N(0, Iₙ)
--   - encoding: second scenario: discrete finitely supported D, zero mass on ∥z∥ ≤ 1, centers with n^{0.49} ≤ ∥µ∥ ≤ √(n log n), ∆min = 1, r ≡ 1 → IsProbabilityMeasure D, (Supp D).Finite, IsSeparatedAtomic 1 D, D(closedBall 0 1) = 0, the norm bounds on every µ ∈ Supp D; sample law mixture D; reason: each clause of the page is one hypothesis; r ≡ 1 makes Mix(D, r) the homogeneous mixture D ∗ N(0, Iₙ)
--   - encoding: any algorithm … correctly distinguishes … with success probability at least 9/10 must use exp(Ω(n log n)) samples → ∃ c > 0, n₀, ∀ n ≥ n₀, ∀ m, ∀ Markov kernel A : (Fin m → ℝⁿ) ⇝ Bool succeeding w.p. ≥ 9/10 in each scenario (every second-scenario D), exp(c · n · log n) ≤ m; reason: a randomized algorithm using at most m samples on every run is such a kernel; Ω with an explicit constant and threshold
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 3, p.5 (PDF p.7), restated p.37 (PDF p.39); Mix(D, r) pp.2–3

import Mathlib
import Definitions.Def_GaussMixHH_CenterModel

open MeasureTheory ProbabilityTheory

namespace GaussMixHH.Supplement

open GaussMixHH

/-- **Theorem 3** (Heterogeneous mixture — estimation lower bound).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 3, p.5 (PDF p.7), restated
p.37 (PDF p.39); `Mix(D, r)` on pp.2–3.

"Any algorithm that is given access to i.i.d. samples from D′ = Mix(D, r) and correctly
distinguishes between the following two scenarios with success probability at least 9/10 must use
exp(Ω(n log n)) samples: • First scenario: D is a point distribution putting all its mass on the
single center 0ⁿ, and r(0ⁿ) = 4. • Second scenario: D is a discrete finitely supported distribution
putting zero mass on any point z ∈ Rⁿ with ∥z∥ ≤ 1; in fact D puts all its mass on centers µ with
n^{0.49} ≤ ∥µ∥ ≤ √(n log n). Moreover, D has minimum separation ∆min = 1 and the squared radius
function r maps every µ ∈ Supp(D) to 1."

**Formalization Note.**
* "Any algorithm" with a worst-case budget of `m` samples is any Markov kernel
  `A : (Fin m → ℝⁿ) ⇝ Bool` (internal randomness included; output `true` = "first scenario"). It
  may depend on `n` and `m` in any way and is not restricted to a machine model. Its output law on
  sample law `Q` is `(Q^{⊗m}).bind A`.
* First scenario: `Mix(δ₀, r)` with `r(0) = 4` is `N(0, 4Iₙ)`, the image of `N(0, Iₙ)` under
  `x ↦ 2x`.
* Second scenario: every probability measure `D` with finite `Supp D` (positive-weight atoms),
  `IsSeparatedAtomic 1 D` (all mass on `Supp D`, distinct atoms at distance `≥ 1`) and
  `D({z : ∥z∥ ≤ 1}) = 0` (stated as on the page; for `n ≥ 2` it follows from the norm bounds) and
  `n^{0.49} ≤ ∥µ∥ ≤ √(n log n)` for every `µ ∈ Supp D`; the sample law is `Mix(D, 1) = mixture D`.
  The test must succeed on every such `D`.
* `Ω(n log n)`: one `c > 0` and a threshold `n₀`, chosen before `n` (for small `n` the second
  scenario may be empty). `log` is `Real.log`. -/
theorem theorem_3 :
    ∃ (c : ℝ) (n₀ : ℕ), 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n →
      ∀ (m : ℕ) (A : Kernel (Fin m → EuclideanSpace ℝ (Fin n)) Bool), IsMarkovKernel A →
        9 / 10 ≤ (((Measure.pi fun _ : Fin m =>
            (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => (2 : ℝ) • x)).bind A)
            {true}).toReal →
        (∀ (D : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure D],
          (Supp D).Finite → IsSeparatedAtomic 1 D →
          D (Metric.closedBall 0 1) = 0 →
          (∀ μ ∈ Supp D, (n : ℝ) ^ (0.49 : ℝ) ≤ ‖μ‖ ∧ ‖μ‖ ≤ Real.sqrt (n * Real.log n)) →
          9 / 10 ≤ (((Measure.pi fun _ : Fin m => mixture D).bind A) {false}).toReal) →
        Real.exp (c * n * Real.log n) ≤ (m : ℝ) := by sorry

end GaussMixHH.Supplement
