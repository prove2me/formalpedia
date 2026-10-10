-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_newtonianPotential_laplacian
-- name    : HunterPDE.Newtonian.newtonianPotential_laplacian
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:14:40.102828+00:00
-- url     : https://prove2.me/theorems/58d7d6fd-6837-40c1-9c2c-66b8eb1301ee
-- title:
--   Eq. (2.23) — Γ ∗ (Δf) = −f for f ∈ C_c^∞(ℝⁿ)
-- statement:
--   Let $n \ge 2$ and let $f \in C_c^\infty(\mathbb{R}^n)$ be smooth with compact support. Then the convolution of the Laplacian of $f$ with the fundamental solution recovers $-f$:
--   $$\Gamma * (\Delta f) = -f, \qquad\text{i.e.}\qquad \int_{\mathbb{R}^n} \Gamma(x - y)\,\Delta f(y)\,dy = -f(x) \quad\text{for every } x \in \mathbb{R}^n.$$
--   This is the heart of the proof of Theorem 2.25: it represents a test function as the Newtonian potential of its own Laplacian.
--
--   **Formalization Note.** $\Delta$ is Mathlib's Laplacian on the inner-product space `EuclideanSpace ℝ (Fin n)` (the sum of pure second partial derivatives in an orthonormal basis). The statement first asserts that $y \mapsto \Gamma(x-y)\,\Delta f(y)$ is Lebesgue integrable for every $x$, so the identity is between genuine integrals. "Smooth" is `ContDiff ℝ ∞` (not `ContDiff ℝ ⊤`, which in this Mathlib means analytic), and compact support is `HasCompactSupport`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 36, Eq. (2.23)

import Mathlib
import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_NewtonianPotential

namespace HunterPDE.Newtonian

open MeasureTheory
open scoped ContDiff
open Laplacian

/-- Hunter, *Notes on PDEs*, p. 36, Eq. (2.23): for `f ∈ C_c^∞(ℝⁿ)`, `n ≥ 2`,
`Γ ∗ (Δf) = −f`, i.e. `∫ Γ(x − y) Δf(y) dy = −f(x)` for every `x`; the first conjunct records
that this integral is a genuine Lebesgue integral for every `x`. `Δ` is Mathlib's Laplacian
on the inner product space `EuclideanSpace ℝ (Fin n)` (the sum of the pure second partial
derivatives in any orthonormal basis). -/
theorem newtonianPotential_laplacian (n : ℕ) (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (∀ x, Integrable (fun y => fundamentalSolution n (x - y) * (Δ f) y)) ∧
      ∀ x, newtonianPotential n (Δ f) x = -f x := by sorry

end HunterPDE.Newtonian
