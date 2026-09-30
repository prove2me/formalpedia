-- Prove2me | Theorems.Thm_FriedmannEquations_density_scaling_of_fluidEq
-- name    : FriedmannEquations.density_scaling_of_fluidEq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T22:53:35.957987+00:00
-- url     : https://prove2.me/theorems/25ac882a-358d-40bd-8419-087e192f7153
-- title:
--   Density scaling $\rho \propto a^{-3(1+w)}$ from the fluid equation with $p = w\rho$
-- statement:
--   Let $w\in\mathbb R$ and let $I$ be an open, (pre)connected time interval on which the scale factor $a$ is positive and differentiable and the density $\rho$ is differentiable. If the fluid equation with equation of state $p = w\rho$,
--   $$\dot\rho = -3H(\rho + w\rho),\qquad H = \dot a/a,$$
--   holds at every $t\in I$, then there is a constant $C$ with
--   $$\rho(t) = C\,a(t)^{-3(1+w)}\qquad\text{for all } t\in I.$$
-- source:
--   Wikipedia, "Friedmann equations", revision oldid=1374073387, https://en.wikipedia.org/w/index.php?title=Friedmann_equations&oldid=1374073387 (the PDF supplied with this proposal), section "Mixtures", pp. 8–9.

import Definitions.Def_FriedmannEquations_Defs
import Mathlib

open FriedmannEquations

theorem FriedmannEquations.density_scaling_of_fluidEq
    (w : ℝ) (R ρ : ℝ → ℝ) (I : Set ℝ) (hI_open : IsOpen I) (hI_conn : IsPreconnected I)
    (hR_pos : ∀ t ∈ I, 0 < R t) (hR : DifferentiableOn ℝ R I) (hρ : DifferentiableOn ℝ ρ I)
    (hfluid : ∀ t ∈ I, FluidEq R ρ (fun s => w * ρ s) t) :
    ∃ C : ℝ, ∀ t ∈ I, ρ t = C * R t ^ (-3 * (1 + w)) := by sorry
