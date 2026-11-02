-- Prove2me | Theorems.Thm_Grunbaum2003_boundary_carrier_frontier_and_homeomorphism
-- name    : Grunbaum2003.boundary_carrier_frontier_and_homeomorphism
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:29:27.97339+00:00
-- url     : https://prove2.me/theorems/4b43d8a0-cc10-4d37-aa2b-fedd0088c67c
-- title:
--   Exposed-face boundary carriers are frontiers and are homeomorphic
-- statement:
--   Let $P$ be a nonempty full-dimensional polytope in $\mathbb R^d$, and let $\mathcal B(P)$ consist of its proper exposed faces, including the empty face. Then
--
--   $$\bigcup_{F\in\mathcal B(P)}F=\partial P.$$
--
--   For every other nonempty full-dimensional polytope $Q$ in the same ambient dimension, their boundary carriers are homeomorphic. This includes dimension zero, where both carriers are empty. This supplies the topological carrier identification needed for boundary refinement; it does not assert that any particular homeomorphism has subcomplex face preimages.
-- source:
--   Grünbaum (2003), Convex Polytopes, §11.1, pp.199–200/PDF239–240, boundary-complex carrier, and supporting-hyperplane characterization in §2.4. Homeomorphism is an application of Mathlib Analysis/Convex/GaugeRescale.lean, exists_homeomorph_image_eq. https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Convex/GaugeRescale.lean

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_boundaryFaces
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

namespace Grunbaum2003

theorem boundary_carrier_frontier_and_homeomorphism (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    (⋃₀ boundaryFaces P = frontier P) ∧
      ∀ Q : Set (Fin d → ℝ), IsDPolytope Q →
        Nonempty ((⋃₀ boundaryFaces P) ≃ₜ (⋃₀ boundaryFaces Q)) := by sorry

end Grunbaum2003
