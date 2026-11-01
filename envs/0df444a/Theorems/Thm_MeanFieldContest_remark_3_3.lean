-- Prove2me | Theorems.Thm_MeanFieldContest_remark_3_3
-- name    : MeanFieldContest.remark_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:59.9883+00:00
-- url     : https://prove2.me/theorems/76342abb-6915-4406-936b-bdc551d0bdb6
-- title:
--   Remark 3.3 — the same when $g(y_1)=c$, and $F(0)=y_2$ if $y_1=0$ (corrected: $R$ not a.e. constant on $(0,1)$)
-- statement:
--   In the setting of Lemma 3.2, with the same added hypothesis that $R$ is not a.e. constant on $(0,1)$, assume also $g(y_1)=c$. Then
--   $$F^{-1}(y_1)\vee0=F^{-1}(y_1+)=F^{-1}(y_2),$$
--   and if $y_1=0$, then $F(0)=y_2$.
--
--   This locates the atom when the flat segment contains its left endpoint, for instance the atom at the origin when $R$ is flat near $r=1$.
--
--   Differences from the source:
--   - correction: §3.1: R any decreasing function → additionally R(r₂) < R(r₁) for some 0 < r₁ < r₂ < 1; reason: the printed statement is false: R(0) = 2, R = 1 on (0,1], µ = 0, x₀ = σ = 1, F = Exp(1) is an equilibrium with y₁ = 0, y₂ = 1, and it is no point mass; the proof uses the added fact in case (ii), “y₁ > 0 as g is not a.e. constant” (p.9); §3.2’s assumptions imply it
--   - reading: §3.1: “R is any decreasing function in this subsection” → R antitone on [0,1], with no continuity, sign or gap condition; reason: the literal hypothesis of §3.1
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: F⁻¹(y₁) = −∞ at y₁ = 0 → Lean’s sInf of an unbounded set is 0; reason: both give F⁻¹(y₁) ∨ 0 = 0
--   - encoding: x₂ = F⁻¹(y₂), with value +∞ allowed → the set {x : y₂ ≤ F(x)} is claimed nonempty, and x₂ is its infimum; reason: the printed equality forces finiteness
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Remark 3.3, p.9; hypothesis of §3.1, p.7

import Mathlib
import Definitions.Def_MeanFieldContest_Model
import Definitions.Def_MeanFieldContest_EnvelopeObjects

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Remark 3.3** (corrected), arXiv:2103.04219v1, p.9. If in Lemma 3.2 also `g(y₁) = c`, then
`x₁ = x₁⁺ = x₂` for `x₁ = F⁻¹(y₁) ∨ 0`; in particular, if `y₁ = 0` then `F(0) = y₂`.

**Formalization Note.** Same correction `hnc` as Lemma 3.2; on the same counterexample `g(y₁) = c`
and `F(0) = 0 ≠ y₂`. At `y₁ = 0` the paper's `F⁻¹(0)` is `−∞` and Lean's `sInf` of the unbounded set
is `0`, and both give `F⁻¹(y₁) ∨ 0 = 0`. -/
theorem remark_3_3 {x₀ μ σ : ℝ} {R : ℝ → ℝ} {F : Measure ℝ} {c y₁ y₂ : ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : AntitoneOn R (Icc 0 1))
    (hnc : ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ r₂ < 1 ∧ R r₂ < R r₁)
    (hF : IsMFE x₀ μ σ R F)
    (hy₁ : y₁ = sInf {y | y ∈ Icc (0 : ℝ) 1 ∧ g R y = c})
    (hy₂ : y₂ = sSup {y | y ∈ Icc (0 : ℝ) 1 ∧ g R y = c}) (hlt : y₁ < y₂)
    (hc : g R y₁ = c) :
    {x | y₂ ≤ cdf F x}.Nonempty ∧ max (quantile F y₁) 0 = quantileRight F y₁ ∧
      quantileRight F y₁ = quantile F y₂ ∧ (y₁ = 0 → cdf F 0 = y₂) := by sorry

end MeanFieldContest
