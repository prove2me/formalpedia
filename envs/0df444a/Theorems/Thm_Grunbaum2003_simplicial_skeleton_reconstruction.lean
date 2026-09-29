-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_skeleton_reconstruction
-- name    : Grunbaum2003.simplicial_skeleton_reconstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T07:05:47.905985+00:00
-- url     : https://prove2.me/theorems/4d01dd96-0264-47e7-baaa-cce13c2c6dcc
-- title:
--   Perles theorem — Simplicial polytopes from half-dimensional skeletons
-- statement:
--   If a simplicial d-polytope and an arbitrary e-polytope have order-equivalent floor(d/2)-skeleton face posets, then e=d and the supplied skeleton equivalence extends to an order equivalence of their complete face posets.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §12.4, “Simplicial polytopes,” Perles reconstruction theorem, printed p. 234a / PDF p. 277; dimensional unambiguity threshold §12.2, printed pp. 226–227 / PDF pp. 268–269; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

namespace Grunbaum2003

/-- Perles's simplicial reconstruction theorem, Grünbaum (2003), §12.4,
“Simplicial polytopes”, printed p.234a / PDF277. The floor(d/2)-skeleton
of a simplicial d-polytope determines its dimension and entire face lattice,
and every given skeleton equivalence extends. The target is any polytope,
not assumed simplicial or of the same dimension. This combines exactly the
strong, weak and dimensional unambiguity stated in that paragraph, using
the meanings in §12.1 pp.225–226 and the cited §12.2.1.
Natural division implements floor(d/2). Existing concrete face subtypes
include the empty face; all orders are inclusion. No algorithm or complexity
bound is asserted. Proof intentionally omitted. -/
theorem simplicial_skeleton_reconstruction (d e : ℕ)
    (P : Set (Fin d → ℝ)) (Q : Set (Fin e → ℝ))
    (hP : IsSimplicialDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d / 2) ≃o SkeletonFace Q (d / 2)) :
    e = d ∧ ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P (d / 2), Φ F.val = (φ F).val := by sorry

end Grunbaum2003
