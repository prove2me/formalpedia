-- Prove2me | Theorems.Thm_MeanFieldContest_theorem_2_2_uniqueness
-- name    : MeanFieldContest.theorem_2_2_uniqueness
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:12.312628+00:00
-- url     : https://prove2.me/theorems/e7e08752-820f-4df1-bda2-426333749b7d
-- title:
--   Proof of Theorem 2.2—Uniqueness — every equilibrium has cdf $F^*$
-- statement:
--   Let $R$ be a reward function and $\mu<\bar\mu_\infty$. Every mean field equilibrium $F$ has cdf
--   $$F(x)=F^*(x)=g^{-1}\big([R(1)+(\bar R-R(1))h(x)]\wedge R(0)\big),\quad x\ge0,$$
--   and $F(x)=0$ for $x<0$.
--
--   This assembles Lemmas 3.1–3.9 into the uniqueness half of Theorem 2.2.
--
--   Differences from the source:
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: g⁻¹ on [R(1), R(0)] → g⁻¹(z) = 1 ∧ inf{y ∈ [0,1] : g(y) > z} for every real z; reason: the paper’s own extension on p.18; it agrees with p.5 on [R(1), R(0)]
--   - encoding: F*(x) on x ≥ 0 → F*(x) := 0 for x < 0; reason: distributions on [0,∞)
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Proof of Theorem 2.2—Uniqueness, pp.16–17

import Mathlib
import Definitions.Def_MeanFieldContest_Model

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Proof of Theorem 2.2—Uniqueness**, arXiv:2103.04219v1, pp.16–17. If `µ < µ̄∞`, every mean field equilibrium has
cdf `F*` of (2.3). -/
theorem theorem_2_2_uniqueness {x₀ μ σ : ℝ} {R : ℝ → ℝ} {F : Measure ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : IsRewardFunction R) (hμ : μ < muBarInfty R x₀ σ)
    (hF : IsMFE x₀ μ σ R F) :
    ∀ x, cdf F x = FStar x₀ μ σ R x := by sorry

end MeanFieldContest
