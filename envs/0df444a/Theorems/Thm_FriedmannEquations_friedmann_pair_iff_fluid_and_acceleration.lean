-- Prove2me | Theorems.Thm_FriedmannEquations_friedmann_pair_iff_fluid_and_acceleration
-- name    : FriedmannEquations.friedmann_pair_iff_fluid_and_acceleration
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T23:23:40.59356+00:00
-- url     : https://prove2.me/theorems/afcd7644-2404-4a7e-abaf-f5aea963e773
-- title:
--   The two Friedmann equations $\iff$ fluid equation + acceleration equation ($k$ as a constant of integration)
-- statement:
--   Let $G > 0$ and $\Lambda\in\mathbb R$, and let $I\subseteq\mathbb R$ be an open, (pre)connected time interval. Let $R$ be a scale factor that is positive and $C^2$ on $I$, let the density $\rho$ be differentiable on $I$, and let $p$ be any pressure function. Then the following are equivalent:
--
--   1. there is a constant $k\in\mathbb R$ such that for every $t\in I$ both Friedmann equations hold:
--   $$\Big(\frac{\dot R}{R}\Big)^2 = \frac{8\pi G\rho}{3} - \frac{k}{R^2} + \frac{\Lambda}{3},\qquad \frac{\ddot R}{R} = \frac{\Lambda}{3} - \frac{4\pi G}{3}(\rho+3p);$$
--   2. for every $t\in I$ the fluid equation $\dot\rho = -3\frac{\dot R}{R}(\rho+p)$ and the acceleration equation $\frac{\ddot R}{R} = \frac{\Lambda}{3} - \frac{4\pi G}{3}(\rho+3p)$ hold.
--
--   This is the statement of the section *Interpretation*: "The pair of equations given above is equivalent to the following pair of equations … with $k$, the spatial curvature index, serving as a constant of integration for the first equation." Units $c = 1$ (so $\kappa c^4 = 8\pi G$).
-- source:
--   Wikipedia, "Friedmann equations", revision oldid=1374073387, https://en.wikipedia.org/w/index.php?title=Friedmann_equations&oldid=1374073387 (the PDF supplied with this proposal), section "Interpretation" (p. 6), together with the equations of section "FLRW models" (pp. 5–6) and "Equations" (p. 2); units $c=1$.

import Definitions.Def_FriedmannEquations_Defs
import Mathlib

open FriedmannEquations

theorem FriedmannEquations.friedmann_pair_iff_fluid_and_acceleration
    (G Λ : ℝ) (hG : 0 < G) (R ρ p : ℝ → ℝ) (I : Set ℝ)
    (hI_open : IsOpen I) (hI_conn : IsPreconnected I)
    (hR_pos : ∀ t ∈ I, 0 < R t) (hR : ContDiffOn ℝ 2 R I) (hρ : DifferentiableOn ℝ ρ I) :
    (∃ k : ℝ, ∀ t ∈ I, FirstFriedmannEq G Λ k R ρ t ∧ SecondFriedmannEq G Λ R ρ p t) ↔
      (∀ t ∈ I, FluidEq R ρ p t ∧ SecondFriedmannEq G Λ R ρ p t) := by sorry
