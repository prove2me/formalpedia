-- Prove2me | Theorems.Thm_NewtonGravitation_pointForce_eq_smul_pointField
-- name    : NewtonGravitation.pointForce_eq_smul_pointField
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:41:40.924331+00:00
-- url     : https://prove2.me/theorems/3e9c2263-7f79-4886-8b14-a436fca94b0d
-- title:
--   Force from the field: $F = m\,g(r)$
-- statement:
--   Let $m_1,m_2\in\mathbb{R}$ and $r_1,r_2\in\mathbb{E}^3$, and let $g$ be the gravitational field of the point mass $m_1$ at $r_1$, $g(x) = -\frac{G m_1}{\|x-r_1\|^3}(x-r_1)$. Then the force exerted on the body of mass $m_2$ at $r_2$ is
--   $$F_{21} = m_2\, g(r_2).$$
--
--   This is the identity $F = m\,g(r)$ of the source's *Gravity field* section: the field is the force per unit mass.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem pointForce_eq_smul_pointField (m₁ m₂ : ℝ) (r₁ r₂ : Space) :
    pointForce m₁ m₂ r₁ r₂ = m₂ • pointField m₁ r₁ r₂ := by sorry

end NewtonGravitation
