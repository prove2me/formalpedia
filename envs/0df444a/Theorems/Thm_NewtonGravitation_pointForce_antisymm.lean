-- Prove2me | Theorems.Thm_NewtonGravitation_pointForce_antisymm
-- name    : NewtonGravitation.pointForce_antisymm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:32:25.847091+00:00
-- url     : https://prove2.me/theorems/ddbfb2bb-d787-4864-9a60-f3660ee9477a
-- title:
--   Newton's third law for gravity: $F_{12} = -F_{21}$
-- statement:
--   Let $m_1, m_2\in\mathbb{R}$ and $r_1,r_2\in\mathbb{E}^3$. Writing $F_{21} = F(m_1,m_2,r_1,r_2)$ for the force on body 2 exerted by body 1 and $F_{12} = F(m_2,m_1,r_2,r_1)$ for the force on body 1 exerted by body 2,
--   $$F_{12} = -F_{21}.$$
--
--   This is the observation in the source's *Vector form* section that gravitational forces between two bodies are equal and opposite.
--
--   **Formalization Note** No hypotheses are needed: at $r_1=r_2$ both sides are $0$ by the division-by-zero convention.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem pointForce_antisymm (m₁ m₂ : ℝ) (r₁ r₂ : Space) :
    pointForce m₂ m₁ r₂ r₁ = -pointForce m₁ m₂ r₁ r₂ := by sorry

end NewtonGravitation
