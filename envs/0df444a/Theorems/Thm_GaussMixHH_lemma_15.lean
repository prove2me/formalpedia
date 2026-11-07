-- Prove2me | Theorems.Thm_GaussMixHH_lemma_15
-- name    : GaussMixHH.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:39.878816+00:00
-- url     : https://prove2.me/theorems/0edf7471-96a1-423a-9035-33e44619a025
-- title:
--   Lemma 15, p.22 — a set $\Theta\subseteq[0,C\alpha]$ of measure $\ge c\alpha^2$ with $|\mathrm{Diff}_\nu|\ge e^{-CA}$ on it
-- statement:
--   There are universal constants $c,C>0$ such that the following holds. Let $\nu$ be a finite real signed measure on $[0,\infty)$ with total variation at most two, $n\in\mathbb N$, $T\ge1$, $0<\beta\le1$, and $|G_\nu(-T)|\ge\beta$. Set
--
--   $$L=\log\frac2\beta,\qquad \alpha=\Big(\frac{TL}{n}\Big)^{1/3},\qquad A=(TL)^{2/3}n^{1/3}.$$
--
--   If $n\ge CTL$, there is a Lebesgue-measurable set $\Theta\subseteq[0,C\alpha]$ with
--
--   $$|\Theta|\ge c\alpha^2\qquad\text{and}\qquad|\mathrm{Diff}_\nu(\theta)|\ge e^{-CA}\ \text{ for every }\theta\in\Theta.$$
--
--   This upgrades one useful frequency to a set of useful frequencies of measure $\Omega(\alpha^2)$, which is what allows a single frequency interval to work for all pairs of distributions (Proposition 19).
--
--   **Formalization Note** $\nu=\mu_1-\mu_2$ with finite measures $\mu_1,\mu_2$ vanishing on $(-\infty,0)$ and $\mu_1(\mathbb R)+\mu_2(\mathbb R)\le2$.
--
--   Differences from the source:
--   - encoding: ν a finite real signed measure on [0, ∞) with total variation norm at most two → ν = μ₁ − μ₂, μ₁, μ₂ finite measures on ℝ vanishing on (−∞, 0) with μ₁(ℝ) + μ₂(ℝ) ≤ 2; reason: Jordan decomposition: the same class of ν; G_ν and Diff_ν depend only on ν
--   - encoding: universal constants c, C → ∃ c C > 0 before all data, one C for n ≥ CTL, [0, Cα] and e^{−CA}; reason: the convention of p.19; each use is monotone in C
--   - encoding: |Θ| ≥ cα² → ENNReal.ofReal (cα²) ≤ volume Θ; reason: Lebesgue measure in ℝ≥0∞
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 15, p.22 (PDF p.24); G_ν, Diff_ν defined p.18

import Mathlib
import Definitions.Def_GaussMixHH_RadialTransform

open MeasureTheory Complex

namespace GaussMixHH

/-- **Lemma 15** (A lower bound on the measure of useful frequencies).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 15, p.22 (PDF p.24); `G_ν`
and `Diff_ν` are defined on p.18.

"Let ν be a finite real signed measure on [0, ∞) with total variation norm at most two. Suppose that
T ≥ 1, 0 < β ≤ 1, and |G_ν(−T)| ≥ β. Set L = log(2/β), α = (TL/n)^{1/3}, A = (TL)^{2/3}n^{1/3}. If
n ≥ CTL, there is a measurable set Θ ⊆ [0, Cα] such that |Θ| ≥ cα², |Diff_ν(θ)| ≥ e^{−CA} for every
θ ∈ Θ. Here |Θ| denotes Lebesgue measure."

**Formalization Note.**
* `ν = μ₁ − μ₂` with finite measures `μ₁, μ₂` on `ℝ` vanishing on `(−∞, 0)` and
  `μ₁(ℝ) + μ₂(ℝ) ≤ 2`. By the Jordan decomposition these are exactly the finite real signed
  measures on `[0, ∞)` of total variation at most two, and `G_ν`, `Diff_ν` depend only on `ν`.
* `c, C` are universal and chosen before all data; one `C` serves the hypothesis `n ≥ CTL`, the
  interval `[0, Cα]` and the exponent `e^{−CA}`.
* Powers `(·)^{1/3}`, `(·)^{2/3}` are `Real.rpow` of positive reals (`n ≥ CTL > 0`). `|Θ|` is
  `volume Θ`. -/
theorem lemma_15 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (μ₁ μ₂ : Measure ℝ), IsFiniteMeasure μ₁ → IsFiniteMeasure μ₂ →
        μ₁ (Set.Iio 0) = 0 → μ₂ (Set.Iio 0) = 0 → μ₁ Set.univ + μ₂ Set.univ ≤ 2 →
        ∀ (n : ℕ) (T β : ℝ), 1 ≤ T → 0 < β → β ≤ 1 →
          β ≤ ‖Gfun μ₁ (-(T : ℂ)) - Gfun μ₂ (-(T : ℂ))‖ →
          let L := Real.log (2 / β)
          let α := (T * L / n) ^ ((1 : ℝ) / 3)
          let A := (T * L) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 3)
          C * T * L ≤ n →
          ∃ Θ : Set ℝ, Θ ⊆ Set.Icc 0 (C * α) ∧ MeasurableSet Θ ∧
            ENNReal.ofReal (c * α ^ 2) ≤ volume Θ ∧
            ∀ θ ∈ Θ, Real.exp (-(C * A)) ≤ ‖DiffNu n μ₁ μ₂ θ‖ := by sorry

end GaussMixHH
