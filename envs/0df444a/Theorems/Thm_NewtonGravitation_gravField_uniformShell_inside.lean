-- Prove2me | Theorems.Thm_NewtonGravitation_gravField_uniformShell_inside
-- name    : NewtonGravitation.gravField_uniformShell_inside
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T19:00:34.655946+00:00
-- url     : https://prove2.me/theorems/f54d81e4-b448-432c-af88-27fa2ce9875b
-- title:
--   Hollow sphere: zero field inside a uniform shell
-- statement:
--   Let $\sigma_{M,a}$ be a uniform spherical shell of mass $M\ge0$ and radius $a>0$ centred at the origin. Then at every interior point $x$, $\|x\|<a$,
--   $$g_{\sigma_{M,a}}(x) = 0.$$
--
--   This is the source's statement that "within a shell of uniform thickness and density there is no net gravitational acceleration anywhere within the hollow sphere", and the interior case of the hollow-sphere formula in the *Gravity field* section.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem gravField_uniformShell_inside (M : NNReal) (a : ℝ) (ha : 0 < a)
    (x : Space) (hx : ‖x‖ < a) :
    gravField (uniformShell M a) x = 0 := by sorry

end NewtonGravitation
