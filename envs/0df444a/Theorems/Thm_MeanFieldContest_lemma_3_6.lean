-- Prove2me | Theorems.Thm_MeanFieldContest_lemma_3_6
-- name    : MeanFieldContest.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:59.75323+00:00
-- url     : https://prove2.me/theorems/7e8a0e6a-3b98-4a32-84ab-3a34ae4d2a0a
-- title:
--   Lemma 3.6 — an interior jump of $g$ gives a flat stretch of $F$
-- statement:
--   Let $R$ be any decreasing function on $[0,1]$, let $J(g)=\{y\in(0,1):g(y-)<g(y+)\}$, and let $F$ be a mean field equilibrium. For each $y\in J(g)$, the set
--   $$\{x\ge0:F(x)=y\}$$
--   has positive length.
--
--   Jumps of the reward therefore force gaps in the support of the equilibrium.
--
--   Differences from the source:
--   - reading: §3.1: “R is any decreasing function in this subsection” → R antitone on [0,1], with no continuity, sign or gap condition; reason: the literal hypothesis of §3.1
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: “has positive length” → positive Lebesgue measure; reason: the set is an interval
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Lemma 3.6, p.10

import Mathlib
import Definitions.Def_MeanFieldContest_Model
import Definitions.Def_MeanFieldContest_EnvelopeObjects

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Lemma 3.6**, arXiv:2103.04219v1, p.10. Let `F` be a mean field equilibrium. For each `y ∈ J(g)`, the interval
`{x ≥ 0 : F(x) = y}` has positive length.

**Formalization Note.** §3.1's hypothesis: `R` is any decreasing function. "Positive length" is
positive Lebesgue measure. -/
theorem lemma_3_6 {x₀ μ σ : ℝ} {R : ℝ → ℝ} {F : Measure ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : AntitoneOn R (Icc 0 1)) (hF : IsMFE x₀ μ σ R F) :
    ∀ y ∈ jumpSet R, 0 < volume {x : ℝ | 0 ≤ x ∧ cdf F x = y} := by sorry

end MeanFieldContest
