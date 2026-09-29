-- Prove2me | Theorems.Thm_MaxwellWiki_div_curl_eq_zero
-- name    : MaxwellWiki.div_curl_eq_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T19:55:44.116858+00:00
-- url     : https://prove2.me/theorems/bfb20ca7-878d-4b15-b79d-b8bd99386288
-- title:
--   Div–curl identity: $\nabla\cdot(\nabla\times F)=0$
-- statement:
--   **Div–curl identity.** Let $F:\mathbb{R}^3\to\mathbb{R}^3$ be a vector field of class $C^2$. Then at every point $x\in\mathbb{R}^3$,
--   $$\nabla\cdot(\nabla\times F)(x)=0 .$$
--
--   This is the vector-calculus identity invoked in the *Charge conservation* section to show that the left-hand side $\nabla\times\mathbf B$ of the Ampère–Maxwell law has zero divergence.
--
--   **Formalization Note** $C^2$ regularity is assumed so that mixed second partial derivatives commute; divergence and curl are those of the shared definition file.
-- source:
--   Wikipedia, "Maxwell's equations", https://en.wikipedia.org/wiki/Maxwell%27s_equations (24-page PDF snapshot supplied by the proposer), section "Charge conservation" (p. 8 of the snapshot): "The left-hand side of the Ampère–Maxwell law has zero divergence by the div–curl identity."

import Mathlib
import Definitions.Def_MaxwellWiki_Defs

open MaxwellWiki

namespace MaxwellWiki

theorem div_curl_eq_zero (F : Vec3 → Vec3) (hF : ContDiff ℝ 2 F) (x : Vec3) :
    div (curl F) x = 0 := by sorry

end MaxwellWiki
