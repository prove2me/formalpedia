-- Prove2me | Theorems.Thm_GeomDL_WL_wl_cannot_distinguish_cycle6_twoTriangles
-- name    : GeomDL.WL.wl_cannot_distinguish_cycle6_twoTriangles
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:58.105826+00:00
-- url     : https://prove2.me/theorems/7de75546-486a-4ad7-864a-629a473c479a
-- title:
--   Side-note p. 120 — the WL test cannot distinguish a 6-cycle from two triangles
-- statement:
--   Let $C_6$ be the cycle on six nodes and $2K_3$ the disjoint union of two triangles. For every round $s$, the multisets of Weisfeiler–Lehman colours of the two graphs coincide,
--   $$
--   \{\!\{c^s_{C_6}(u) : u \in V(C_6)\}\!\} = \{\!\{c^s_{2K_3}(u) : u \in V(2K_3)\}\!\},
--   $$
--   yet $C_6$ and $2K_3$ are not isomorphic.
--
--   This is the standard example showing that the WL test is only a necessary condition for isomorphism.
--
--   **Formalization Note** The WL test is the featureless 1-WL colour refinement `neighborColor` / `neighborHistogram` of the reused definition `WLIdentification`.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), Ch. 7, side-note p. 120, "One simple example: the WL test cannot distinguish a 6-cycle from two triangles."

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_GeomDL_WL_Defs

namespace GeomDL.WL
open OAI.WLIdentification

/-- Side-note p. 120: the WL test cannot distinguish a 6-cycle from two triangles. The colour
histograms of `C₆` and `2K₃` agree at every round, although the graphs are not isomorphic. -/
theorem wl_cannot_distinguish_cycle6_twoTriangles :
    (∀ s, neighborHistogram cycle6 s = neighborHistogram twoTriangles s) ∧
      ¬ Isomorphic cycle6 twoTriangles := by sorry

end GeomDL.WL
