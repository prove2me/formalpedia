-- Prove2me | Theorems.Thm_NumStochOpt_Bounds_eq_2_32_2_34_edmundson_madansky_one_dim
-- name    : NumStochOpt.Bounds.eq_2_32_2_34_edmundson_madansky_one_dim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T19:08:46.083953+00:00
-- url     : https://prove2.me/theorems/da547d52-9b5d-4d2f-94d5-fbf92c15fdb7
-- title:
--   Eqs. (2.32)–(2.34) — the one-dimensional Edmundson–Madansky inequality
-- statement:
--   Let $\xi$ be a real random variable on a probability space $(\Omega,P)$ with values in $[a,b]$ almost surely, $a<b$, and mean $\xi^0=E\xi$. Let $\hat\xi$ take the value $a$ with probability $p_1=(b-\xi^0)/(b-a)$ and $b$ with probability $p_2=(\xi^0-a)/(b-a)$ (2.32). If $\varphi$ is convex on $[a,b]$, then
--   $$
--   E\varphi(\xi)\;\le\;E\varphi(\hat\xi)=\frac{b-\xi^0}{b-a}\,\varphi(a)+\frac{\xi^0-a}{b-a}\,\varphi(b). \tag{2.33}
--   $$
--
--   Applied to $\varphi=Q(x,\cdot)$, convex by property (b) when $q$ is deterministic, this is the upper bound $EQ(x,\xi)\le EQ(x,\hat\xi)$ of (2.33)–(2.34), complementing Jensen's lower bound.
--
--   **Formalization Note** The book writes the inequality for $\varphi=Q(x,\cdot)$; it is stated here for any function convex on $[a,b]$. The book says $\xi$ has support $[a,b]$; the statement only needs $\xi\in[a,b]$ almost surely. The case $a=b$, where (2.32) divides by zero, is excluded by $a<b$.
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, pp. 45-46, Eqs. (2.32)-(2.34)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky

open MeasureTheory

namespace NumStochOpt.Bounds

/-- Eqs. (2.32)–(2.34), pp. 45–46: the one-dimensional Edmundson–Madansky inequality. If `ξ`
takes values in `[a, b]` (`a < b`) with mean `ξ⁰ = E ξ` and `φ` is convex on `[a, b]`, then
`E φ(ξ) ≤ p₁ φ(a) + p₂ φ(b)` with `p₁ = (b − ξ⁰)/(b − a)`, `p₂ = (ξ⁰ − a)/(b − a)`. -/
theorem eq_2_32_2_34_edmundson_madansky_one_dim {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Ω → ℝ) (hξ : AEMeasurable ξ P)
    (a b : ℝ) (hab : a < b) (hsupp : ∀ᵐ ω ∂P, ξ ω ∈ Set.Icc a b)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc a b) φ) :
    ∫ ω, φ (ξ ω) ∂P ≤
      emProb a b (∫ ω, ξ ω ∂P) false * φ a + emProb a b (∫ ω, ξ ω ∂P) true * φ b := by sorry

end NumStochOpt.Bounds
