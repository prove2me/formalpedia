-- Prove2me | Theorems.Thm_MeanFieldContest_theorem_2_2_existence
-- name    : MeanFieldContest.theorem_2_2_existence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:22.579549+00:00
-- url     : https://prove2.me/theorems/cd41ae79-cfb0-4179-a7e3-492c2089695c
-- title:
--   Proof of Theorem 2.2—Existence — the law with cdf $F^*$ is an equilibrium
-- statement:
--   Let $R$ be a reward function, $x_0,\sigma>0$ and $\mu<\bar\mu_\infty$. There is a probability measure $F$ whose cdf is
--   $$F^*(x)=g^{-1}\big([R(1)+(\bar R-R(1))h(x)]\wedge R(0)\big),\quad x\ge0,$$
--   with $F^*=0$ on $(-\infty,0)$, and $F$ is a mean field equilibrium.
--
--   This is the verification half of Theorem 2.2.
--
--   Differences from the source:
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: g⁻¹ on [R(1), R(0)] → g⁻¹(z) = 1 ∧ inf{y ∈ [0,1] : g(y) > z} for every real z; reason: the paper’s own extension on p.18; it agrees with p.5 on [R(1), R(0)]
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Proof of Theorem 2.2—Existence, pp.6–7

import Mathlib
import Definitions.Def_MeanFieldContest_Model

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Proof of Theorem 2.2—Existence**, arXiv:2103.04219v1, pp.6–7. If `µ < µ̄∞`, the distribution with cdf `F*`
of (2.3) is feasible and is a mean field equilibrium. -/
theorem theorem_2_2_existence {x₀ μ σ : ℝ} {R : ℝ → ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : IsRewardFunction R) (hμ : μ < muBarInfty R x₀ σ) :
    ∃ F : Measure ℝ, (∀ x, cdf F x = FStar x₀ μ σ R x) ∧ IsMFE x₀ μ σ R F := by sorry

end MeanFieldContest
