-- Prove2me | Theorems.Thm_MeanFieldContest_lemma_3_2
-- name    : MeanFieldContest.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:55.667065+00:00
-- url     : https://prove2.me/theorems/9eff6f0f-a2c6-49ad-88e1-e964dfd621c1
-- title:
--   Lemma 3.2 — a flat segment of $g$ is an atom of every equilibrium (corrected: $R$ not a.e. constant on $(0,1)$)
-- statement:
--   Let $R$ be decreasing on $[0,1]$ and not a.e. constant on $(0,1)$: $R(r_1)>R(r_2)$ for some $0<r_1<r_2<1$. Suppose $g$ has a flat segment at level $c$, that is,
--   $$y_1=\inf\{y\in[0,1]:g(y)=c\}<y_2=\sup\{y\in[0,1]:g(y)=c\},$$
--   and let $F$ be a mean field equilibrium. Then $x_2=F^{-1}(y_2)$ is finite, $x_1^+:=F^{-1}(y_1+)$ equals $x_2$, and
--   $$F(x_1^+-)=y_1,\qquad F(x_1^+)=y_2.$$
--
--   Ranks with equal reward are thus occupied by players stopping at one single level.
--
--   Differences from the source:
--   - correction: §3.1: R any decreasing function → additionally R(r₂) < R(r₁) for some 0 < r₁ < r₂ < 1; reason: the printed statement is false: R(0) = 2, R = 1 on (0,1], µ = 0, x₀ = σ = 1, F = Exp(1) is an equilibrium with y₁ = 0, y₂ = 1, and it is no point mass; the proof uses the added fact in case (ii), “y₁ > 0 as g is not a.e. constant” (p.9); §3.2’s assumptions imply it
--   - reading: §3.1: “R is any decreasing function in this subsection” → R antitone on [0,1], with no continuity, sign or gap condition; reason: the literal hypothesis of §3.1
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: x₂ = F⁻¹(y₂), with value +∞ allowed → the set {x : y₂ ≤ F(x)} is claimed nonempty, and x₂ is its infimum; reason: the printed equality x₁⁺ = x₂ forces finiteness, while Lean’s sInf ∅ would be 0
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Lemma 3.2, p.8; hypothesis of §3.1, p.7; case (ii) of the proof, p.9

import Mathlib
import Definitions.Def_MeanFieldContest_Model
import Definitions.Def_MeanFieldContest_EnvelopeObjects

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Lemma 3.2** (corrected), arXiv:2103.04219v1, p.8. Suppose `g` has a flat segment at level `c`, so that
`y₁ = inf{y ∈ [0,1] : g(y) = c}` and `y₂ = sup{y ∈ [0,1] : g(y) = c}` satisfy `y₁ < y₂`, and let `F`
be a mean field equilibrium. Then `x₁⁺ := F⁻¹(y₁+)` equals `x₂ := F⁻¹(y₂)`, `F(x₁⁺−) = y₁` and
`F(x₁⁺) = y₂`.

**Formalization Note.** Correction: `hnc`, "`R` is not a.e. constant on `(0,1)`", is added. The page's
§3.1 hypotheses ("any decreasing function") make the lemma false: `R(0) = 2`, `R = 1` on `(0,1]`,
`µ = 0`, `x₀ = σ = 1` and `F = Exp(1)` is an equilibrium with `y₁ = 0`, `y₂ = 1`, and it is no point
mass. The proof uses the added fact in case (ii): "`y₁ > 0` as `g` is not a.e. constant" (p.9). No
continuity of `R` is assumed. The finiteness of `F⁻¹(y₂)` is part of the claim
(`{x | y₂ ≤ F(x)}` nonempty): the printed equality forces it, while Lean's `sInf ∅` would be `0`. -/
theorem lemma_3_2 {x₀ μ σ : ℝ} {R : ℝ → ℝ} {F : Measure ℝ} {c y₁ y₂ : ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : AntitoneOn R (Icc 0 1))
    (hnc : ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ r₂ < 1 ∧ R r₂ < R r₁)
    (hF : IsMFE x₀ μ σ R F)
    (hy₁ : y₁ = sInf {y | y ∈ Icc (0 : ℝ) 1 ∧ g R y = c})
    (hy₂ : y₂ = sSup {y | y ∈ Icc (0 : ℝ) 1 ∧ g R y = c}) (hlt : y₁ < y₂) :
    {x | y₂ ≤ cdf F x}.Nonempty ∧ quantileRight F y₁ = quantile F y₂ ∧
      F.real (Iio (quantileRight F y₁)) = y₁ ∧ cdf F (quantileRight F y₁) = y₂ := by sorry

end MeanFieldContest
