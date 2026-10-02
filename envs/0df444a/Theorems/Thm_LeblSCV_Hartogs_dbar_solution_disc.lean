-- Prove2me | Theorems.Thm_LeblSCV_Hartogs_dbar_solution_disc
-- name    : LeblSCV.Hartogs.dbar_solution_disc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:47:26.925258+00:00
-- url     : https://prove2.me/theorems/b652062d-e2b0-488a-8829-a6c5d1cf6525
-- title:
--   Lemma 4.4.6 — solving ∂ψ/∂z̄ = g on a disc by the Cauchy transform
-- statement:
--   Let $U = \{\zeta \in \mathbb{C} : |\zeta - c| < r\}$ be an open disc with $r > 0$, and let $g$ be a smooth function on an open neighborhood $V$ of the closed disc $\overline{U}$. Define $\psi : U \to \mathbb{C}$ by
--   $$\psi(z) = \frac{1}{2\pi i} \int_U \frac{g(\zeta)}{\zeta - z}\, d\zeta \wedge d\bar\zeta, \qquad d\zeta \wedge d\bar\zeta = (-2i)\,dA.$$
--   Then for every $z \in U$ the integrand is integrable on $U$, the function $\psi$ is smooth ($C^\infty$) on $U$, and $\dfrac{\partial \psi}{\partial \bar z} = g$ on $U$.
--
--   This solves the inhomogeneous $\bar\partial$-equation in one variable; the same integral, in the first variable with the others as parameters, is the solution operator in Theorem 4.2.1.
--
--   **Formalization Note.** Restriction: the book states the lemma for any bounded open set with piecewise-$C^1$ boundary; here $U$ is a disc. The function $\psi$ is a total function `ℂ → ℂ` constrained by the formula only on $U$; since $U$ is open, its values off $U$ do not affect smoothness on $U$ or $\partial\psi/\partial\bar z$ at points of $U$. Smooth is `ContDiffOn ℝ ∞` (real $C^\infty$, not analytic). Integrability of the integrand is part of the conclusion.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 141, Lemma 4.4.6

import Mathlib
import Definitions.Def_LeblSCV_Shared_dbar

open Complex MeasureTheory
open scoped Real
open scoped ContDiff

namespace LeblSCV.Hartogs

/-- Lemma 4.4.6 (Lebl, p. 141), for `U` an open disc `{|ζ - c| < r}`, `r > 0`. Let `g` be smooth
on an open neighborhood `V` of the closed disc `Ū`. Define `ψ : U → ℂ` by
`ψ(z) = (1/2πi) ∫_U g(ζ)/(ζ - z) dζ ∧ dζ̄`, with `dζ ∧ dζ̄ = (-2i) dA` (p. 130). Then for every
`z ∈ U` the integrand is integrable on `U`, `ψ` is smooth on `U`, and `∂ψ/∂z̄ = g` on `U`.
(`ψ` is given only on `U`; its values off `U` are unconstrained and do not enter the conclusion,
because `U` is open.) -/
theorem dbar_solution_disc {c : ℂ} {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ∃ V : Set ℂ, IsOpen V ∧ Metric.closedBall c r ⊆ V ∧ ContDiffOn ℝ ∞ g V)
    (ψ : ℂ → ℂ)
    (hψ : ∀ z ∈ Metric.ball c r,
      ψ z = (2 * π * I)⁻¹ * ((-2 * I) * ∫ ζ in Metric.ball c r, g ζ / (ζ - z))) :
    (∀ z ∈ Metric.ball c r, IntegrableOn (fun ζ : ℂ => g ζ / (ζ - z)) (Metric.ball c r)) ∧
      ContDiffOn ℝ ∞ ψ (Metric.ball c r) ∧
      ∀ z ∈ Metric.ball c r, LeblSCV.Shared.dbar ψ z = g z := by sorry

end LeblSCV.Hartogs
