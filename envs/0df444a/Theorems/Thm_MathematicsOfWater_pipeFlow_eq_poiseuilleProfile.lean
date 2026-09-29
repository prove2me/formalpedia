-- Prove2me | Theorems.Thm_MathematicsOfWater_pipeFlow_eq_poiseuilleProfile
-- name    : MathematicsOfWater.pipeFlow_eq_poiseuilleProfile
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:39:47.34362+00:00
-- url     : https://prove2.me/theorems/efd6f11b-3ae5-41bd-b12c-2d3580b13299
-- title:
--   Boundary conditions force the parabolic Poiseuille profile
-- statement:
--   Consider steady pressure-driven flow along a cylindrical pipe of diameter $d>0$ and length $L>0$, filled with a Newtonian fluid of viscosity $\eta>0$, with pressure drop $\Delta p=p(0)-p(L)\in\mathbb R$. Let $v(r)$ be the axial velocity at distance $r$ from the axis and assume
--
--   1. $v$ solves $\frac1r\frac{d}{dr}\big(r\frac{dv}{dr}\big)=-\frac{\Delta p}{\eta L}$ for $0<r<d/2$ (with the needed differentiability);
--   2. $v$ stays finite at the axis: $v$ is bounded on $(0,d/2)$;
--   3. no-slip at the wall: $v(d/2)=0$, with $v$ continuous at $r=d/2$ from inside.
--
--   Then for every $0<r\le d/2$,
--
--   $$v(r)=\frac{\Delta p}{4\eta L}\Big(\frac{d^2}{4}-r^2\Big).$$
--
--   This is the parabolic Hagen–Poiseuille velocity profile: fastest at the centre, zero at the wall.
--
--   **Formalization Note** "$v(r=0)<\infty$" is encoded as boundedness of $v$ on $(0,d/2)$; the value of $v$ at $r=0$ itself is unconstrained, so the conclusion is stated on $(0,d/2]$. The hypotheses are packaged in the definition `IsPipeFlow`.
-- source:
--   Lecture 15: The Mathematics of Water, PHYS 461 & 561 (Biophysics), Drexel University, Fall 2011-2012, 11/15/2011, lecturer Luis Cruz (for Brigita Urbanc), www.physics.drexel.edu/~brigita/COURSES/BIOPHYS_2011-2012/, slide 16 (boundary conditions and "final expression for the fluid velocity in the pipe")

import Mathlib
import Definitions.Def_MathematicsOfWater_PipeFlow
open Real

namespace MathematicsOfWater
theorem pipeFlow_eq_poiseuilleProfile (η L Δp d : ℝ) (v : ℝ → ℝ)
    (hη : 0 < η) (hL : 0 < L) (hd : 0 < d)
    (hv : IsPipeFlow η L Δp d v) :
    ∀ r ∈ Set.Ioc 0 (d / 2), v r = poiseuilleProfile η L Δp d r := by sorry
end MathematicsOfWater
