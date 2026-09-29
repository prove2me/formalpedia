-- Prove2me | Theorems.Thm_NewtonGravitation_gravField_uniformShell_outside
-- name    : NewtonGravitation.gravField_uniformShell_outside
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T19:12:06.735928+00:00
-- url     : https://prove2.me/theorems/c2fed641-225e-4d50-883b-56a0ba6c964f
-- title:
--   Hollow sphere: exterior field equals the point-mass field
-- statement:
--   Let $\sigma_{M,a}$ be a uniform spherical shell of mass $M\ge0$ and radius $a>0$ centred at the origin. Then at every exterior point $x$, $\|x\|>a$,
--   $$g_{\sigma_{M,a}}(x) = -\frac{GM}{\|x\|^3}\,x .$$
--
--   This is the exterior case of the hollow-sphere formula in the source's *Gravity field* section ($|g| = GM/r^2$ for $r\ge R$).
--
--   **Formalization Note** The source writes $r\ge R$. At a point on the shell itself ($r=R$) the field integral of a uniform surface density diverges (the integrand is not integrable), so the Lean statement uses the strict inequality $\|x\|>a$; on the shell the Lean integral would be $0$ by convention.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem gravField_uniformShell_outside (M : NNReal) (a : ℝ) (ha : 0 < a)
    (x : Space) (hx : a < ‖x‖) :
    gravField (uniformShell M a) x = pointField M 0 x := by sorry

end NewtonGravitation
