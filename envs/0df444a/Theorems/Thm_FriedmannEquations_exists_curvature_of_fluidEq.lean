-- Prove2me | Theorems.Thm_FriedmannEquations_exists_curvature_of_fluidEq
-- name    : FriedmannEquations.exists_curvature_of_fluidEq
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T21:45:08.768552+00:00
-- url     : https://prove2.me/theorems/4a2d39fc-e8f1-4099-8ddd-0e927df26c21
-- title:
--   Fluid + acceleration equations give the first Friedmann equation with a constant of integration $k$
-- statement:
--   Let $G,\Lambda\in\mathbb R$ and let $I$ be an open, (pre)connected time interval on which the scale factor $R$ is positive and $C^2$ and the density $\rho$ is differentiable. Suppose that at every $t\in I$ the fluid equation
--   $$\dot\rho = -3\frac{\dot R}{R}(\rho + p)$$
--   and the acceleration equation
--   $$\frac{\ddot R}{R} = \frac{\Lambda}{3} - \frac{4\pi G}{3}(\rho + 3p)$$
--   hold. Then there is a constant $k\in\mathbb R$ such that the first Friedmann equation
--   $$\Big(\frac{\dot R}{R}\Big)^2 = \frac{8\pi G\rho}{3} - \frac{k}{R^2} + \frac{\Lambda}{3}$$
--   holds at every $t\in I$. Units $c = 1$.
-- source:
--   Wikipedia, "Friedmann equations", revision oldid=1374073387, https://en.wikipedia.org/w/index.php?title=Friedmann_equations&oldid=1374073387 (the PDF supplied with this proposal), section "Interpretation", p. 6.

import Definitions.Def_FriedmannEquations_Defs
import Mathlib

open FriedmannEquations

theorem FriedmannEquations.exists_curvature_of_fluidEq
    (G Λ : ℝ) (R ρ p : ℝ → ℝ) (I : Set ℝ) (hI_open : IsOpen I) (hI_conn : IsPreconnected I)
    (hR_pos : ∀ t ∈ I, 0 < R t) (hR : ContDiffOn ℝ 2 R I) (hρ : DifferentiableOn ℝ ρ I)
    (hfluid : ∀ t ∈ I, FluidEq R ρ p t)
    (h₂ : ∀ t ∈ I, SecondFriedmannEq G Λ R ρ p t) :
    ∃ k : ℝ, ∀ t ∈ I, FirstFriedmannEq G Λ k R ρ t := by sorry
