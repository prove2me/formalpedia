-- Prove2me | Theorems.Thm_KarpPapadimitriou_SmallFacial_zero_one_vertices
-- name    : KarpPapadimitriou.SmallFacial.zero_one_vertices
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:40:24.404138+00:00
-- url     : https://prove2.me/theorems/1f095ffd-a980-4288-8a43-8a7139c64fe4
-- title:
--   Zero-one hulls have zero-one vertices and no rays
-- statement:
--   Let $C=(L,n,S)$ be a zero-one problem and let $z\in L$. Every vertex of $\mathrm{CH}(S(z))$ is a zero-one vector, and this hull has no nonzero ray:
--   $$\operatorname{vert}(\mathrm{CH}(S(z)))\subseteq\{0,1\}^{n(z)},\qquad \operatorname{ray}(\mathrm{CH}(S(z)))=\varnothing.$$
--   This supplies the bounded geometric case in the proof of Lemma 1, including an empty feasible set.
--
--   **Formalization Note** A ray means a nonzero rational direction $d$ and a base point $v$ in the hull with $v+td$ in the hull for every rational $t\ge0$. A vertex is an extreme point. The hull is over $\mathbb Q$, as in the paper's notation.
-- source:
--   Karp & Papadimitriou, MIT/LCS/TM-154 (Feb. 1980), p. 6, proof of Lemma 1, zero-one case; https://dspace.mit.edu/server/api/core/bitstreams/eb122126-c312-4445-a8d2-153e3e7d285f/content

import Mathlib
import Definitions.Def_KarpPapadimitriou_SmallFacial_COP

namespace KarpPapadimitriou.SmallFacial

/-- p. 6, proof of Lemma 1: zero-one hulls have zero-one vertices and no rays. -/
theorem zero_one_vertices (C : COP) (hC : IsZeroOne C) (z : List Bool) (hz : z ∈ C.L) :
    (∀ v, IsVertex (hull C z) v → ∀ i, v i = 0 ∨ v i = 1) ∧
    ¬ HasRay (hull C z) := by sorry

end KarpPapadimitriou.SmallFacial
