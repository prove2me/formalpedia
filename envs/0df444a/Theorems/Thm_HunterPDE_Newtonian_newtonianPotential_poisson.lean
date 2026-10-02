-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_newtonianPotential_poisson
-- name    : HunterPDE.Newtonian.newtonianPotential_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:19:35.450443+00:00
-- url     : https://prove2.me/theorems/64ac2128-a26d-48fb-80f3-df5723589c0e
-- title:
--   Theorem 2.25 — the Newtonian potential u = Γ ∗ f is C^∞ and solves −Δu = f
-- statement:
--   Let $n \ge 2$, let $f \in C_c^\infty(\mathbb{R}^n)$, and let $u = \Gamma * f$ be its Newtonian potential, where $\Gamma$ is the fundamental solution (2.12). Then $u \in C^\infty(\mathbb{R}^n)$ and $u$ solves Poisson's equation
--   $$-\Delta u = f \quad\text{in } \mathbb{R}^n.$$
--   This is the existence half of the theory of Poisson's equation on the whole space and the starting point for the regularity estimates of this mission.
--
--   **Formalization Note.** The statement has three conjuncts: for every $x$ the integrand $y \mapsto \Gamma(x-y) f(y)$ is Lebesgue integrable (so $u(x)$ is a genuine integral, not Lean's default value $0$ for a non-integrable function), $u$ is `ContDiff ℝ ∞`, and $-\Delta u(x) = f(x)$ for every $x$. The integrability conjunct makes explicit what the book's definition of $\Gamma * f$ presupposes.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 34, Theorem 2.25

import Mathlib
import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Definitions.Def_HunterPDE_Newtonian_NewtonianPotential

namespace HunterPDE.Newtonian

open MeasureTheory
open scoped ContDiff
open Laplacian

/-- Hunter, *Notes on PDEs*, p. 34, Theorem 2.25: if `f ∈ C_c^∞(ℝⁿ)` (`n ≥ 2`) and
`u = Γ ∗ f` with `Γ` the fundamental solution (2.12), then `u ∈ C^∞(ℝⁿ)` and `−Δu = f`
(2.16). The first conjunct records that the convolution integral `∫ Γ(x − y) f(y) dy` defining
`u(x)` is a genuine Lebesgue integral for every `x` (so `u` is not the Bochner junk value `0`).
`ContDiff ℝ ∞` is `C^∞` (not `ContDiff ℝ ⊤`, which is analyticity in this Mathlib). -/
theorem newtonianPotential_poisson (n : ℕ) (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (∀ x, Integrable (fun y => fundamentalSolution n (x - y) * f y)) ∧
      ContDiff ℝ ∞ (newtonianPotential n f) ∧
      ∀ x, -(Δ (newtonianPotential n f)) x = f x := by sorry

end HunterPDE.Newtonian
