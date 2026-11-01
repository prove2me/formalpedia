-- Prove2me | Theorems.Thm_MeanFieldContest_lemma_2_1
-- name    : MeanFieldContest.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:01.932897+00:00
-- url     : https://prove2.me/theorems/21af7870-6c36-4a67-a456-0832484e951a
-- title:
--   Lemma 2.1 — the feasible laws are the distributions on $[0,\infty)$ with $\int h\,dF=1$ ($\mu>0$), $\le 1$ ($\mu\le0$)
-- statement:
--   Let $x_0>0$, $\mu\in\mathbb R$, $\sigma>0$. A player observes $X_t=x+\mu t+\sigma W_t$ absorbed at $0$ and picks a randomized stopping time $\tau<\infty$; $\mathcal F$ is the set of laws of the position at stopping when $x=x_0$.
--
--   Then $\mathcal F$ consists of exactly the distributions $F$ on $[0,\infty)$ with
--   $$\int h\,dF=1\ \text{ if }\mu>0,\qquad \int h\,dF\le1\ \text{ if }\mu\le0.$$
--
--   This is Hall's embedding of distributions into Brownian motion with drift, with absorption at $0$. It turns every perturbation in the analysis of equilibria into a one-line feasibility check.
--
--   **Formalization Note** $\int h\,dF$ is a lower integral of the nonnegative function $h$ on $[0,\infty)$, so a law with infinite integral does not satisfy the constraint.
--
--   Differences from the source:
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: ∫h dF → the lintegral of ofReal∘h; reason: h ≥ 0 on the support, and a Bochner integral would be 0 for a non-integrable h
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Lemma 2.1, p.5

import Mathlib
import Definitions.Def_MeanFieldContest_Model

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Lemma 2.1** (Hall's embedding, with absorption), arXiv:2103.04219v1, p.5. The set `𝓕` of laws of the absorbed
drifted Brownian motion at a randomized finite stopping time consists of all distributions `F` on
`[0,∞)` with `∫h dF = 1` if `µ > 0` and `∫h dF ≤ 1` if `µ ≤ 0`.

**Formalization Note.** `feasibleLaws` is the stochastic set, so this is a theorem with two
inclusions. `∫h dF` is a lower integral of the nonnegative `h` on `[0,∞)`, so a law with infinite
`∫h dF` is not "`≤ 1`" through the Bochner junk value `0`. -/
theorem lemma_2_1 {x₀ μ σ : ℝ} (hx₀ : 0 < x₀) (hσ : 0 < σ) :
    feasibleLaws x₀ μ σ =
      {F : Measure ℝ | IsProbabilityMeasure F ∧ F (Iio 0) = 0 ∧
        (0 < μ → ∫⁻ x, ENNReal.ofReal (scale x₀ μ σ x) ∂F = 1) ∧
        (μ ≤ 0 → ∫⁻ x, ENNReal.ofReal (scale x₀ μ σ x) ∂F ≤ 1)} := by sorry

end MeanFieldContest
