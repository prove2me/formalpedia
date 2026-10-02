-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_secondPartial_newtonianPotential_ball
-- name    : HunterPDE.Newtonian.secondPartial_newtonianPotential_ball
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:26:01.731843+00:00
-- url     : https://prove2.me/theorems/a36744c1-fc4b-4e7b-bb16-8a855be93ea3
-- title:
--   Corollary 2.27 — ∂ᵢⱼu(x) = ∫_{B_R(x)} ∂ᵢⱼΓ(x−y)[f(y)−f(x)] dy − (1/n) f(x) δᵢⱼ
-- statement:
--   Let $n \ge 2$, $f \in C_c^\infty(\mathbb{R}^n)$ and $u = \Gamma * f$. Let $x \in \mathbb{R}^n$ and let $B_R(x)$ be an open ball centered at $x$ containing the support of $f$. Then for all indices $i, j$
--   $$\partial_{ij} u(x) = \int_{B_R(x)} \partial_{ij}\Gamma(x - y)\,\bigl[f(y) - f(x)\bigr]\,dy - \frac{1}{n} f(x)\,\delta_{ij},$$
--   where $\partial_{ij}\Gamma(x - y)$ is the second partial derivative of $\Gamma$ evaluated at $x - y$ and $\delta_{ij}$ is the Kronecker delta. The kernel $\partial_{ij}\Gamma$ is not locally integrable, and the subtraction of $f(x)$ is what makes the integral converge; this representation is the input to the Hölder estimate, Theorem 2.28.
--
--   **Formalization Note.** Indices are 0-based. The statement asserts, as a first conjunct, that $y \mapsto \partial_{ij}\Gamma(x-y)[f(y)-f(x)]$ is Lebesgue integrable on $B_R(x)$ (an absolutely convergent integral, as the book's proof uses), and then the identity. The support is the closed support `tsupport f`, and $R > 0$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 39, Corollary 2.27, Eq. (2.29)

import Mathlib
import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_NewtonianPotential
import Definitions.Def_HunterPDE_Newtonian_PartialDeriv

namespace HunterPDE.Newtonian

open MeasureTheory
open scoped ContDiff

/-- Hunter, *Notes on PDEs*, p. 39, Corollary 2.27: if `f ∈ C_c^∞(ℝⁿ)` (`n ≥ 2`) and
`u = Γ ∗ f`, then for every `x` and every open ball `B_R(x)` centered at `x` that contains the
support of `f`,
`∂ᵢⱼu(x) = ∫_{B_R(x)} ∂ᵢⱼΓ(x − y) [f(y) − f(x)] dy − (1/n) f(x) δᵢⱼ`.
Here `∂ᵢⱼΓ(x − y)` is the second partial derivative of `Γ` evaluated at `x − y`; the integrand
is Lebesgue integrable on the ball (asserted as the first conjunct, as the proof of Theorem 2.26
states). Indices are 0-based. -/
theorem secondPartial_newtonianPotential_ball (n : ℕ) (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R)
    (hsupp : tsupport f ⊆ Metric.ball x R) (i j : Fin n) :
    IntegrableOn (fun y => secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x))
        (Metric.ball x R) ∧
      secondPartial (newtonianPotential n f) i j x =
        (∫ y in Metric.ball x R, secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x))
          - 1 / (n : ℝ) * f x * (if i = j then 1 else 0) := by sorry

end HunterPDE.Newtonian
