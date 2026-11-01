-- Prove2me | Theorems.Thm_MeanFieldContest_theorem_2_2
-- name    : MeanFieldContest.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:12.175115+00:00
-- url     : https://prove2.me/theorems/dbb1b69b-92b6-4ad4-a6c1-96a70624a101
-- title:
--   Theorem 2.2 — the mean field contest has a unique equilibrium, with cdf $F^*$, value $u^*$, support in $[0,\bar x]$, and atoms matching the flat stretches of $R$
-- statement:
--   Let $R:[0,1]\to\mathbb R_+$ be decreasing and right-continuous with $R(0)>R(1-)=R(1)$, let $g(y)=R(1-y)$, $\bar R=\int_0^1R$, and let $h$ be the scale function normalized by $h(x_0)=1$. Let $\mu<\bar\mu_\infty$. Then there exists a unique mean field equilibrium $F$, and:
--
--   1. its cdf is
--   $$F^*(x)=g^{-1}\big([R(1)+(\bar R-R(1))h(x)]\wedge R(0)\big);$$
--   2. its value function is, for a player started at any level $x\ge0$,
--   $$u^*(x)=[R(1)+(\bar R-R(1))h(x)]\wedge R(0);$$
--   3. it has compact support, carried by $[0,\bar x]$ with $0$ and $\bar x$ in the support, where $h(\bar x)=\dfrac{R(0)-R(1)}{\bar R-R(1)}$;
--   4. its atoms are in one-to-one correspondence with the intervals where $R$ is constant: the map sending an atom $x$ to the level set $\{r\in[0,1]:R(r)=R(1-F(x))\}$ is a bijection onto the level sets of $R$ with more than one point.
--
--   This is the main result of the paper: a stochastic game with discontinuous payoffs has one equilibrium, in closed form.
--
--   **Formalization Note** $F^*$ vanishes on the negative half-line. Clause 3 asserts the existence of $\bar x$, which uses $\mu<\bar\mu_\infty$ when $\mu>0$.
--
--   Differences from the source:
--   - reading: “compact support [0, x̄]” → F is concentrated on [0, x̄], and every open neighbourhood of 0 and of x̄ has positive mass; reason: equality of the support with [0, x̄] is false when R jumps (Proposition 3.5, p.10, is a two-point law; Lemma 3.6 gives gaps); this is the strongest true reading, and [0, x̄] is the smallest closed interval carrying F
--   - reading: “its atoms are in one-to-one correspondence with intervals where the reward R is constant” → an explicit bijection x ↦ {r ∈ [0,1] : R(r) = R(1 − F(x))} from the atoms onto the level sets of R with more than one point; reason: level sets of a monotone R are intervals and these are its maximal intervals of constancy; an explicit map is stronger than equinumerosity
--   - reading: “the equilibrium value function is u*” → u^F(x) = u*(x) for every starting level x ≥ 0, with h normalized at x₀; reason: p.5 defines u(x) for “a player starting at level x (instead of x₀)”
--   - encoding: x̄ = h⁻¹((R(0) − R(1))/(R̄ − R(1))) → a real x̄ ≥ 0 with h(x̄) equal to that ratio; reason: h is strictly increasing, so this pins x̄ down, and its existence is part of the claim
--   - encoding: F*(x) on x ≥ 0 → F*(x) := 0 for x < 0; reason: distributions on [0,∞)
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: g⁻¹ on [R(1), R(0)] → g⁻¹(z) = 1 ∧ inf{y ∈ [0,1] : g(y) > z} for every real z; reason: the paper’s own extension on p.18; it agrees with p.5 on [R(1), R(0)]
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Theorem 2.2, p.5

import Mathlib
import Definitions.Def_MeanFieldContest_Model

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Theorem 2.2**, arXiv:2103.04219v1, p.5. Let `µ < µ̄∞`. There exists a unique equilibrium `F`. Its cdf is
`F*(x) = g⁻¹([R(1) + (R̄ − R(1))h(x)] ∧ R(0))`, the equilibrium value function is
`u*(x) = [R(1) + (R̄ − R(1))h(x)] ∧ R(0)`, the equilibrium has compact support `[0, x̄]` for
`x̄ = h⁻¹((R(0) − R(1))/(R̄ − R(1)))`, and its atoms are in one-to-one correspondence with intervals
where the reward `R` is constant.

**Formalization Note.** The value function is stated at every starting level `x ≥ 0`, with `h`
normalized at `x₀`. "Compact support `[0, x̄]`" is read as: `F` is concentrated on `[0, x̄]`, and `0` and
`x̄` are in its support, i.e. `[0, x̄]` is the smallest closed interval carrying `F`. Equality of the
support with the interval is false when `R` jumps (Proposition 3.5, p.10, is a two-point law, and
Lemma 3.6 gives gaps). `x̄` is characterized by `h(x̄) = …` since `h` is strictly increasing, and its
existence is part of the claim. The correspondence is the explicit bijection `x ↦ {r ∈ [0,1] : R(r) =
R(1 − F(x))}` from the atoms onto the level sets of `R` with more than one point; level sets of a
monotone function are intervals, and these are its maximal intervals of constancy. -/
theorem theorem_2_2 {x₀ μ σ : ℝ} {R : ℝ → ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : IsRewardFunction R) (hμ : μ < muBarInfty R x₀ σ) :
    ∃ F : Measure ℝ, IsMFE x₀ μ σ R F ∧ (∀ G, IsMFE x₀ μ σ R G → G = F) ∧
      (∀ x, cdf F x = FStar x₀ μ σ R x) ∧
      (∀ x, 0 ≤ x → valueFn μ σ R F x = uStar x₀ μ σ R x) ∧
      (∃ xbar : ℝ, 0 ≤ xbar ∧ scale x₀ μ σ xbar = (R 0 - R 1) / (Rbar R - R 1) ∧
        F (Icc 0 xbar)ᶜ = 0 ∧
        (∀ U : Set ℝ, IsOpen U → 0 ∈ U → 0 < F U) ∧
        (∀ U : Set ℝ, IsOpen U → xbar ∈ U → 0 < F U)) ∧
      BijOn (fun x : ℝ => {r | r ∈ Icc (0 : ℝ) 1 ∧ R r = R (1 - cdf F x)})
        {x : ℝ | F {x} ≠ 0}
        {S : Set ℝ | ∃ c : ℝ, S = {r | r ∈ Icc (0 : ℝ) 1 ∧ R r = c} ∧ S.Nontrivial} := by sorry

end MeanFieldContest
