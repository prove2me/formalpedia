-- Prove2me | Theorems.Thm_Grunbaum2003_blind_mani_graph_reconstruction
-- name    : Grunbaum2003.blind_mani_graph_reconstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T07:05:32.431366+00:00
-- url     : https://prove2.me/theorems/8b6c4af6-798b-453d-9413-7391e4f40727
-- title:
--   Blind–Mani theorem — Simple polytopes from their graphs
-- statement:
--   For two d-polytopes, if the source has exactly d graph neighbors at every vertex, then every order equivalence of their 1-skeleton face posets extends to an order equivalence of their complete face posets.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §12.4, “Simple polytopes,” Blind–Mani theorem, printed p. 234a / PDF p. 277; ambiguity definitions §12.1, printed pp. 225–226 / PDF pp. 267–268; simplicity convention §4.5, printed p. 58 / PDF p. 82; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_PolytopeVertex
import Definitions.Def_Grunbaum2003_polytopeGraph

set_option autoImplicit false

namespace Grunbaum2003

/-- Blind–Mani theorem, Grünbaum (2003), §12.4, “Simple polytopes”,
printed p.234a / PDF277. Graphs of simple d-polytopes are strongly
and weakly d-unambiguous, in the sense of §12.1 pp.225–226.
Simplicity is expressed by exactly d neighbors at every vertex, reusing
the graph-degree convention of the Eberhard and strict-height packages.
A graph equivalence is encoded by an order equivalence of its 1-skeleton
face posets (empty face, vertices, and edges). Every given equivalence
extends to all faces, retaining both strong and weak unambiguity.
The target is any d-polytope; its simplicity follows from the same graph.
No dimensional-unambiguity or reconstruction-algorithm claim is added. -/
theorem blind_mani_graph_reconstruction (d : ℕ)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (hSimple : ∀ v : PolytopeVertex P,
      ((polytopeGraph P).neighborSet v).ncard = d)
    (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P 1, Φ F.val = (φ F).val := by sorry

end Grunbaum2003
