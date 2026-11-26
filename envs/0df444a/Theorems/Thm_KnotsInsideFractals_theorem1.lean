-- Prove2me | Theorems.Thm_KnotsInsideFractals_theorem1
-- name    : KnotsInsideFractals.theorem1
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T15:08:21.899062+00:00
-- url     : https://prove2.me/theorems/060608c4-ac44-58c8-8898-2c979ab00633
-- title:
--   Theorem 1 (Theorem A) — every knot in the Menger sponge
-- statement:
--   **Theorem 1 (Theorem A).** Every tame knot can be embedded, with its knot type preserved, in a finite iteration of the Menger sponge. Precisely, for every polygonal knot $K$ there exist $n\in\mathbb{N}$ and a polygonal knot $L$ whose image lies in the $1$-skeleton of the $n$-th Menger iteration $M_n$ and which is ambient isotopic to $K$:
--   $$\forall K,\ \exists n,\ \exists L,\quad L\subseteq \text{1-skeleton}(M_n)\ \wedge\ L\sim_{\mathrm{amb}} K.$$
--   Because edges survive all later iterations, such an $L$ also lies in the Menger sponge $M$ itself. This is the central result of the paper, answering its first question. It is proved there by shifting an arc presentation of $K$ onto Cantor-set coordinates and pushing the crossings into the sponge through Cantor-dust points.
-- source:
--   Broden–Espinosa–Nazareth–Voth, Knots Inside Fractals, https://arxiv.org/abs/2409.03639, §3 Theorem 1 (Theorem A)

import Mathlib
import Definitions.Def_KnotsInsideFractals_fractals
import Definitions.Def_KnotsInsideFractals_knots
open Set KnotsInsideFractals

namespace KnotsInsideFractals
theorem theorem1 (K : PolygonalKnot) : ∃ n, EmbedsInMenger K n := by sorry
end KnotsInsideFractals
