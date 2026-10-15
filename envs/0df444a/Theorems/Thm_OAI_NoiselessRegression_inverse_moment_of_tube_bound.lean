-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_inverse_moment_of_tube_bound
-- name    : OAI.NoiselessRegression.inverse_moment_of_tube_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:23:27.332267+00:00
-- url     : https://prove2.me/theorems/66966ede-0120-47a4-bc25-87df301fffdf
-- title:
--   Inverse moments of a nonnegative function from polynomial small-ball bounds
-- statement:
--   Let $(X,\mathcal F)$ be a measurable space, $\mu$ a measure on $X$, $f:X\to\mathbb{R}$ a measurable function with $f(x)\ge0$ for all $x\in X$, $m\in\mathbb{N}$, and $C\in[0,\infty]$. Assume the small-ball (tube) bound
--   $$\mu\big(\{x\in X:\ f(x)\le r\}\big)\le C\,r^{m+1}\qquad\text{for all } r\in(0,1].$$
--   Then
--   $$
--   \int_X f(x)^{-m}\,d\mu(x)\ \le\ \mu(X)+2^{m+1}\,C .
--   $$
--   The integral is the Lebesgue integral of a nonnegative function, computed in $[0,\infty]$, and at points where $f(x)=0$ the integrand $f(x)^{-m}$ is interpreted as $0$ if $m\ge1$ and as $1$ if $m=0$.
--
--   The statement converts a polynomial bound on the measure of the sublevel sets of $f$, with exponent one larger than the order of the moment, into a bound on the $m$-th inverse moment of $f$. It is applied to the distance $f(x)=\operatorname{dist}(x,L)$ from an affine subspace $L$, giving integrability of inverse powers of this distance for measures that do not concentrate near $L$. When $C<\infty$ the hypothesis gives $\mu(\{f=0\})\le C\,r^{m+1}$ for all $r\in(0,1]$, hence $\mu(\{f=0\})=0$, so the convention at zeros of $f$ is then irrelevant.
--
--   **Formalization Note** The integrand is `ENNReal.ofReal ((f x)⁻¹ ^ m)`, which uses Lean's convention $0^{-1}=0$ for the real inverse; this is the source of the interpretation at zeros of $f$. The measure $\mu$ is not assumed finite; if $\mu(X)=\infty$ the bound is trivial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/InverseMoments.lean#L70-L108

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
universe u
variable {X : Type*} [MeasurableSpace X]

theorem OAI.NoiselessRegression.inverse_moment_of_tube_bound (μ : Measure X) (f : X → ℝ) (m : ℕ)
    (hf : Measurable f) (hnonneg : ∀ x, 0 ≤ f x) (C : ℝ≥0∞)
    (htube : ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ {x | f x ≤ r} ≤ C * ENNReal.ofReal (r ^ (m + 1))) :
    ∫⁻ x, ENNReal.ofReal ((f x)⁻¹ ^ m) ∂μ ≤
      μ Set.univ + C * (2 : ℝ≥0∞) ^ (m + 1) := by sorry
