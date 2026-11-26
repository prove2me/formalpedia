-- Prove2me | Theorems.Thm_KnotsInsideFractals_corollary2
-- name    : KnotsInsideFractals.corollary2
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T15:08:40.673799+00:00
-- url     : https://prove2.me/theorems/8b2c4281-3791-5159-bef3-77bb3f4d024c
-- title:
--   Corollary 2 — countably many tame knot types
-- statement:
--   **Corollary 2.** The isotopy classes of tame knots form a countable set. Equivalently, there is a countable set of polygonal knots containing a representative of every ambient-isotopy class:
--   $$\exists\, S\ \text{countable},\ \forall K,\ \exists L\in S,\ L\sim_{\mathrm{amb}} K.$$
--   This classical fact follows from Theorem 1: each knot type appears on the finite $1$-skeleton of some $M_n$, and there are only countably many iterations.
-- source:
--   Broden–Espinosa–Nazareth–Voth, Knots Inside Fractals, https://arxiv.org/abs/2409.03639, §3 Corollary 2

import Mathlib
import Definitions.Def_KnotsInsideFractals_fractals
import Definitions.Def_KnotsInsideFractals_knots
open Set KnotsInsideFractals

namespace KnotsInsideFractals
theorem corollary2 : ∃ (s : Set PolygonalKnot), s.Countable ∧ ∀ K : PolygonalKnot, ∃ L ∈ s, AmbientIsotopic K.set L.set := by sorry
end KnotsInsideFractals
