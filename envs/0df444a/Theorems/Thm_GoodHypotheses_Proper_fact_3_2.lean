-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_fact_3_2
-- name    : GoodHypotheses.Proper.fact_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:14:58.084935+00:00
-- url     : https://prove2.me/theorems/f2d63e91-6232-49c7-8691-c3b75bd49235
-- title:
--   Fact 3.2 — the importance-sampling Scheffé statistic is unbiased for d_TV(f, g)
-- statement:
--   Let $f,g$ be nonnegative integrable densities with Scheffé function $S$, and $\psi,\omega$ densities of distributions with $f\le C_0\psi$ and $g\le C_1\omega$ pointwise for constants $C_0,C_1$. For $X\sim\psi$, $Y\sim\omega$ the statistic
--   $$Z=\frac{f(X)}{\psi(X)}S(X)-\frac{g(Y)}{\omega(Y)}S(Y)+\frac12\Big(\frac{g(Y)}{\omega(Y)}-\frac{f(X)}{\psi(X)}\Big)$$
--   satisfies $\mathbb E[Z]=d_{TV}(f,g)$. It lets unnormalized densities be compared using samples from reference distributions.
--
--   Differences from the source:
--
--   - encoding: nonnegative, integrable densities → functions X → ℝ, nonnegative at every point and μ-integrable (Bochner); reason: the paper's nonnegative integrable densities (Definition 2); integrability keeps every integral genuine
--   - encoding: S a Scheffé function (Definition 3) → IsScheffe and S measurable; reason: the integrals ∫ fS dµ of the statement presuppose that S is measurable
--   - encoding: densities ψ of distributions, draws X ∼ ψ → a ProbabilityMeasure P with P = ψ·μ (IsDensityOf: ψ measurable, nonnegative), X drawn from P; two draws from the product law; reason: Lean represents a draw by its law; independence does not change the expectation of a sum
--   - encoding: E[·] = value → the integrand is integrable for the product law and its integral equals the value; reason: Lean's integral of a non-integrable function is 0; the paper's expectation exists
--   - encoding: f(X)/ψ(X) where ψ(X) = 0 → Lean's a/0 = 0; reason: domination forces f = 0 where ψ = 0; that set has probability zero under ψ·μ, so assigning 0 to the otherwise undefined ratio does not change its expectation
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 14, Fact 3.2

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Densities

open MeasureTheory

namespace GoodHypotheses.Proper

/-- Fact 3.2 (Unbiased Estimation of TV, p. 14): `f, g` nonnegative integrable densities with a
(measurable) Scheffé function `S`; `ψ, ω` densities of the probability laws `Pψ, Pω` with
`f ≤ C₀ ψ` and `g ≤ C₁ ω` pointwise; `X ∼ Pψ`, `Y ∼ Pω` (drawn independently). Then the statistic
`Z = (f(X)/ψ(X)) S(X) − (g(Y)/ω(Y)) S(Y) + (1/2)(g(Y)/ω(Y) − f(X)/ψ(X))` is integrable and
`E[Z] = dTV(f, g)`. -/
theorem fact_3_2 {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g S ψ ω : X → ℝ)
    (Pψ Pω : ProbabilityMeasure X) (C₀ C₁ : ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hf : Integrable f μ) (hg : Integrable g μ)
    (hS : IsScheffe f g S) (hSm : Measurable S)
    (hψ : IsDensityOf μ Pψ ψ) (hω : IsDensityOf μ Pω ω)
    (hfψ : ∀ x, f x ≤ C₀ * ψ x) (hgω : ∀ x, g x ≤ C₁ * ω x) :
    Integrable (fun z : X × X => scheffeStatistic f g S ψ ω z.1 z.2)
        ((Pψ : Measure X).prod (Pω : Measure X)) ∧
      ∫ z, scheffeStatistic f g S ψ ω z.1 z.2 ∂((Pψ : Measure X).prod (Pω : Measure X))
        = tvDist μ f g := by sorry

end GoodHypotheses.Proper
