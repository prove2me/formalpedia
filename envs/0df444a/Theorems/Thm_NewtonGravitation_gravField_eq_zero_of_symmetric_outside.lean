-- Prove2me | Theorems.Thm_NewtonGravitation_gravField_eq_zero_of_symmetric_outside
-- name    : NewtonGravitation.gravField_eq_zero_of_symmetric_outside
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T17:46:48.299661+00:00
-- url     : https://prove2.me/theorems/d2a07c7b-3b47-4e35-9a32-7b3c099382ff
-- title:
--   Shell theorem, interior part: outer mass exerts no net force
-- statement:
--   Let $\mu$ be a finite, spherically symmetric mass distribution on $\mathbb{E}^3$, and let $\rho\in\mathbb{R}$ be such that $\mu$ puts no mass in the open ball $\|y\|<\rho$. Then at every point $x$ with $\|x\|<\rho$,
--   $$g_\mu(x) = 0.$$
--
--   This is the second bullet of Newton's shell theorem in the source: "the portion of the mass that is located at radii $r>r_0$ exerts no net gravitational force at the radius $r_0$ from the center." In particular there is no gravitational field inside a hollow shell of uniform thickness and density.
--
--   **Formalization Note** The strict inequality $\|x\|<\rho$ with no mass below radius $\rho$ keeps the integrand bounded, so the Bochner integral is a genuine integral.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem gravField_eq_zero_of_symmetric_outside (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : IsSphericallySymmetric μ) (ρ : ℝ) (hρ : μ (Metric.ball 0 ρ) = 0)
    (x : Space) (hx : ‖x‖ < ρ) :
    gravField μ x = 0 := by sorry

end NewtonGravitation
