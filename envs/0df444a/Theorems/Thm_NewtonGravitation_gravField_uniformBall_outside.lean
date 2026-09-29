-- Prove2me | Theorems.Thm_NewtonGravitation_gravField_uniformBall_outside
-- name    : NewtonGravitation.gravField_uniformBall_outside
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T19:56:12.634155+00:00
-- url     : https://prove2.me/theorems/a8e1e18c-d358-4fbf-b092-c04b2efe0c20
-- title:
--   Uniform solid sphere: exterior field equals the point-mass field
-- statement:
--   Let $\beta_{M,R}$ be a uniform solid ball of mass $M\ge0$ and radius $R>0$ centred at the origin. Then at every point $x$ with $\|x\|\ge R$ (on or outside the surface),
--   $$g_{\beta_{M,R}}(x) = -\frac{GM}{\|x\|^3}\,x .$$
--
--   This is the case $r\ge R$ of the uniform-solid-sphere formula in the source's *Gravity field* section ($|g| = GM/r^2$ for $r\ge R$), with the direction (towards the centre) made explicit.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem gravField_uniformBall_outside (M : NNReal) (R : ℝ) (hR : 0 < R)
    (x : Space) (hx : R ≤ ‖x‖) :
    gravField (uniformBall M R) x = pointField M 0 x := by sorry

end NewtonGravitation
