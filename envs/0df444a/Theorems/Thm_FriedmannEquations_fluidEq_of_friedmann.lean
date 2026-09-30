-- Prove2me | Theorems.Thm_FriedmannEquations_fluidEq_of_friedmann
-- name    : FriedmannEquations.fluidEq_of_friedmann
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T21:41:04.031509+00:00
-- url     : https://prove2.me/theorems/e12bfeb3-6cd7-4bd3-8f0a-b64d89a8e184
-- title:
--   The Friedmann equations imply the fluid equation $\dot\rho = -3H(\rho + p)$
-- statement:
--   Let $G>0$, $\Lambda, k\in\mathbb R$, and let $I$ be an open time set on which the scale factor $R$ is positive and $C^2$ and the density $\rho$ is differentiable. If both Friedmann equations
--   $$H^2 = \frac{8\pi G\rho}{3} - \frac{k}{R^2} + \frac{\Lambda}{3},\qquad \frac{\ddot R}{R} = \frac{\Lambda}{3} - \frac{4\pi G}{3}(\rho+3p)$$
--   hold at every $t\in I$ (with $H = \dot R/R$ and the same constant $k$), then the fluid equation
--   $$\dot\rho = -3H(\rho + p)$$
--   holds at every $t\in I$. Units $c=1$.
-- source:
--   Wikipedia, "Friedmann equations", revision oldid=1374073387, https://en.wikipedia.org/w/index.php?title=Friedmann_equations&oldid=1374073387 (the PDF supplied with this proposal), section "Equations", p. 2 (display after "Using the first equation, the second equation can be re-expressed as").

import Definitions.Def_FriedmannEquations_Defs
import Mathlib

open FriedmannEquations

theorem FriedmannEquations.fluidEq_of_friedmann
    (G Λ k : ℝ) (hG : 0 < G) (R ρ p : ℝ → ℝ) (I : Set ℝ) (hI_open : IsOpen I)
    (hR_pos : ∀ t ∈ I, 0 < R t) (hR : ContDiffOn ℝ 2 R I) (hρ : DifferentiableOn ℝ ρ I)
    (h₁ : ∀ t ∈ I, FirstFriedmannEq G Λ k R ρ t)
    (h₂ : ∀ t ∈ I, SecondFriedmannEq G Λ R ρ p t) :
    ∀ t ∈ I, FluidEq R ρ p t := by sorry
