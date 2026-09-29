-- Prove2me | Theorems.Thm_NewtonGravitation_gravField_uniformBall_inside
-- name    : NewtonGravitation.gravField_uniformBall_inside
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T19:52:42.963906+00:00
-- url     : https://prove2.me/theorems/b2d1af35-0c40-404b-8494-ee6cdb40af1c
-- title:
--   Uniform solid sphere: interior field $g = -GMx/R^3$
-- statement:
--   Let $\beta_{M,R}$ be a uniform solid ball of mass $M\ge0$ and radius $R>0$ centred at the origin. Then at every interior point $x$, $\|x\|<R$,
--   $$g_{\beta_{M,R}}(x) = -\frac{GM}{R^3}\,x .$$
--
--   This is the interior case of the uniform-solid-sphere formula in the source's *Gravity field* section ($|g| = GMr/R^3$ for $r<R$): the field grows linearly with the distance from the centre.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem gravField_uniformBall_inside (M : NNReal) (R : ℝ) (hR : 0 < R)
    (x : Space) (hx : ‖x‖ < R) :
    gravField (uniformBall M R) x = -(G * M / R ^ 3) • x := by sorry

end NewtonGravitation
