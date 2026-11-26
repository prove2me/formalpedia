-- Prove2me | Theorems.Thm_KnotsInsideFractals_conjecture1
-- name    : KnotsInsideFractals.conjecture1
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T15:10:29.810009+00:00
-- url     : https://prove2.me/theorems/5bc0e9f8-9346-45f5-9862-91835812b0ed
-- title:
--   Conjecture 1 (open) — every knot in the Sierpinski tetrahedron
-- statement:
--   **Conjecture 1 (open).** Every tame knot can be embedded in a finite iteration of the Sierpinski tetrahedron:
--   $$\forall K,\ \exists n,\ K\ \text{embeds in the 1-skeleton of}\ S_n.$$
--   The authors prove this for pretzel knots (Theorem 2) but leave the general case open, seeing no real impediment. This is the paper's main open question, strengthening Theorem 2.
-- source:
--   Broden–Espinosa–Nazareth–Voth, Knots Inside Fractals, https://arxiv.org/abs/2409.03639, §4 Conjecture 1

import Mathlib
import Definitions.Def_KnotsInsideFractals_fractals
import Definitions.Def_KnotsInsideFractals_knots
open Set KnotsInsideFractals

namespace KnotsInsideFractals
theorem conjecture1 (K : PolygonalKnot) : ∃ n, EmbedsInSierpinski K n := by sorry
end KnotsInsideFractals
