-- Prove2me | Theorems.Thm_KnotsInsideFractals_lemma3
-- name    : KnotsInsideFractals.lemma3
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T15:08:59.822606+00:00
-- url     : https://prove2.me/theorems/0eff763e-2799-57b9-a79c-d8ad23ef4f17
-- title:
--   Lemma 3 — skeleton comparison preserves knot type
-- statement:
--   **Lemma 3 (knot-type preservation).** Every polygonal knot contained in the $1$-skeleton of the $n$-th Sierpinski iteration $S_n$ is ambient isotopic to a polygonal knot contained in the $1$-skeleton of the $n$-th Menger iteration $M_n$:
--   $$K\subseteq \text{1-skeleton}(S_n)\ \Longrightarrow\ \exists L\subseteq \text{1-skeleton}(M_n),\ L\sim_{\mathrm{amb}} K.$$
--   This is the knot-type-preserving content of the paper's skeleton embedding $i_n:S_n\hookrightarrow M_n$, constructed inductively by substituting coloured copies of the first iteration; the substitutions occur in disjoint regions and create no extra knotting. It is the step underlying Theorem 3.
-- source:
--   Broden–Espinosa–Nazareth–Voth, Knots Inside Fractals, https://arxiv.org/abs/2409.03639, §5 Lemma 3

import Mathlib
import Definitions.Def_KnotsInsideFractals_fractals
import Definitions.Def_KnotsInsideFractals_knots
open Set KnotsInsideFractals

namespace KnotsInsideFractals
theorem lemma3 (n : ℕ) (K : PolygonalKnot) (hK : K.set ⊆ sierpinskiSkeleton n) : ∃ L : PolygonalKnot, L.set ⊆ mengerSkeleton n ∧ AmbientIsotopic K.set L.set := by sorry
end KnotsInsideFractals
