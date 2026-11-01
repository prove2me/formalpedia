-- Prove2me | Theorems.Thm_MeanFieldContest_lemma_3_1
-- name    : MeanFieldContest.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:52.109307+00:00
-- url     : https://prove2.me/theorems/2e4d9fc5-a34c-460d-9b0f-417b2bf10aec
-- title:
--   Lemma 3.1 — atoms of an equilibrium sit on flat stretches of $g$, and $\xi^F=g\circ F$
-- statement:
--   Let $R$ be any decreasing function on $[0,1]$ and $F$ a mean field equilibrium. If $F$ has an atom at $x_1\ge0$, then $g$ is constant on
--   $$(F(x_1-),F(x_1)].$$
--   As a result, $\xi^F(x)=g(F(x))$ for all $x\ge0$.
--
--   So in equilibrium no tie is ever paid less than its top rank, and players tied at a level all earn the same reward.
--
--   Differences from the source:
--   - reading: §3.1: “R is any decreasing function in this subsection” → R antitone on [0,1], with no continuity, sign or gap condition; reason: the literal hypothesis of §3.1
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Lemma 3.1, p.7

import Mathlib
import Definitions.Def_MeanFieldContest_Model

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Lemma 3.1**, arXiv:2103.04219v1, p.7. Let `F ∈ 𝓕` be a mean field equilibrium. If `F` has an atom at
`x₁ ∈ ℝ₊`, then `g` is constant on `(F(x₁−), F(x₁)]`. As a result, `ξ^F(x) = g(F(x))` for all
`x ∈ ℝ₊`.

**Formalization Note.** §3.1 (p.7): "`R` is any decreasing function in this subsection", so the only
assumption on `R` is that it is antitone on `[0,1]`. -/
theorem lemma_3_1 {x₀ μ σ : ℝ} {R : ℝ → ℝ} {F : Measure ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : AntitoneOn R (Icc 0 1)) (hF : IsMFE x₀ μ σ R F) :
    (∀ x₁ : ℝ, 0 ≤ x₁ → F {x₁} ≠ 0 →
      ∀ y ∈ Ioc (F.real (Iio x₁)) (cdf F x₁), g R y = g R (cdf F x₁)) ∧
    ∀ x : ℝ, 0 ≤ x → xi R F x = g R (cdf F x) := by sorry

end MeanFieldContest
