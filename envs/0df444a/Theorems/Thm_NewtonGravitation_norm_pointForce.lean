-- Prove2me | Theorems.Thm_NewtonGravitation_norm_pointForce
-- name    : NewtonGravitation.norm_pointForce
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:39:52.297354+00:00
-- url     : https://prove2.me/theorems/512cac2f-c9a4-48ec-9cc9-dcabc4ff1bd9
-- title:
--   Magnitude of the gravitational force: $F = G m_1 m_2 / r^2$
-- statement:
--   Let $m_1,m_2\ge 0$ be masses located at distinct points $r_1\neq r_2$ of $\mathbb{E}^3$. Then the vector force $F_{21}$ has magnitude
--   $$\|F_{21}\| = \frac{G\,m_1 m_2}{\|r_2-r_1\|^2}.$$
--
--   This recovers the scalar form $F = G m_1 m_2 / r^2$ of Newton's law from the vector form, as stated in the source's *Vector form* section.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem norm_pointForce (m₁ m₂ : ℝ) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (r₁ r₂ : Space)
    (hr : r₁ ≠ r₂) :
    ‖pointForce m₁ m₂ r₁ r₂‖ = G * m₁ * m₂ / ‖r₂ - r₁‖ ^ 2 := by sorry

end NewtonGravitation
