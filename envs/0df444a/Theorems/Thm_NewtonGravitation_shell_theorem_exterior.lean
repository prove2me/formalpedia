-- Prove2me | Theorems.Thm_NewtonGravitation_shell_theorem_exterior
-- name    : NewtonGravitation.shell_theorem_exterior
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T20:02:35.354806+00:00
-- url     : https://prove2.me/theorems/ee1e88e4-9015-487e-b3ee-0ac8a7bb75c1
-- title:
--   Shell theorem: a spherically symmetric body attracts like a point mass
-- statement:
--   Let $\mu$ be a finite, spherically symmetric mass distribution on $\mathbb{E}^3$ (centred at the origin) whose mass is contained in the closed ball $\|y\|\le R$. Then at every point $x$ with $\|x\|>R$,
--   $$g_\mu(x) = -\frac{G\,\mu(\mathbb{E}^3)}{\|x\|^3}\,x,$$
--   i.e. the field of $\mu$ outside its support coincides with the field of a point mass equal to the total mass $\mu(\mathbb{E}^3)$ placed at the centre.
--
--   This is the source's statement that "an object with a spherically symmetric distribution of mass exerts the same gravitational attraction on external bodies as if all the object's mass were concentrated at a point at its center", the result Newton needed to apply his law to planets.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem shell_theorem_exterior (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : IsSphericallySymmetric μ) (R : ℝ) (hR : μ (Metric.closedBall 0 R)ᶜ = 0)
    (x : Space) (hx : R < ‖x‖) :
    gravField μ x = pointField (μ.real Set.univ) 0 x := by sorry

end NewtonGravitation
