-- Prove2me | Theorems.Thm_MathematicsOfWater_radial_equation_general_solution
-- name    : MathematicsOfWater.radial_equation_general_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:34:42.745473+00:00
-- url     : https://prove2.me/theorems/50851834-5d1f-4511-9535-27ee29b18ff9
-- title:
--   General solution of the radial pipe-flow equation
-- statement:
--   Let $\eta>0$ (viscosity), $L>0$ (pipe length), $R>0$, and let $\Delta p\in\mathbb R$ (pressure drop). Suppose $v:\mathbb R\to\mathbb R$ is differentiable on $(0,R)$, that $r\mapsto r\,v'(r)$ is differentiable on $(0,R)$, and that
--
--   $$\frac1r\,\frac{d}{dr}\Big(r\,\frac{dv}{dr}\Big)=-\frac{\Delta p}{\eta L}\qquad(0<r<R).$$
--
--   Then there are constants $C_1,C_2\in\mathbb R$ such that
--
--   $$v(r)=-\frac{\Delta p}{\eta L}\,\frac{r^2}{4}+C_1\ln r+C_2\qquad\text{for all }0<r<R.$$
--
--   This is the step "integrate twice along $r$" of the Hagen–Poiseuille derivation; the boundary conditions are then used to fix $C_1,C_2$.
--
--   **Formalization Note** The slide writes the homogeneous term as $C_1/r^2$; this is a typo in the source, since $r^{-2}$ does not solve $\frac1r(r v')'=0$ while $\ln r$ does. The statement uses $C_1\ln r$. The ODE is packaged in the definition `SatisfiesRadialStokesODE`.
-- source:
--   Lecture 15: The Mathematics of Water, PHYS 461 & 561 (Biophysics), Drexel University, Fall 2011-2012, 11/15/2011, lecturer Luis Cruz (for Brigita Urbanc), www.physics.drexel.edu/~brigita/COURSES/BIOPHYS_2011-2012/, slide 15 ("Integrate both sides along the z direction ..." and "Now integrate twice along r to get a solution")

import Mathlib
import Definitions.Def_MathematicsOfWater_PipeFlow
open Real

namespace MathematicsOfWater
theorem radial_equation_general_solution (η L Δp R : ℝ) (v : ℝ → ℝ)
    (hη : 0 < η) (hL : 0 < L) (hR : 0 < R)
    (hv : SatisfiesRadialStokesODE η L Δp R v) :
    ∃ C₁ C₂ : ℝ, ∀ r ∈ Set.Ioo 0 R,
      v r = -(Δp / (η * L)) * r ^ 2 / 4 + C₁ * Real.log r + C₂ := by sorry
end MathematicsOfWater
