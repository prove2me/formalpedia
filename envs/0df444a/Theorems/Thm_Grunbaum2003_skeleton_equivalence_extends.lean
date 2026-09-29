-- Prove2me | Theorems.Thm_Grunbaum2003_skeleton_equivalence_extends
-- name    : Grunbaum2003.skeleton_equivalence_extends
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T07:05:05.469668+00:00
-- url     : https://prove2.me/theorems/0f19ac90-3555-426e-80b2-cd795b676ea9
-- title:
--   Theorem 12.3.1 — Reconstruction from the (d−2)-skeleton
-- statement:
--   For d ≥ 3, every order equivalence between the (d−2)-skeleton face posets of two d-polytopes extends to an order equivalence of their entire face posets, agreeing with the supplied equivalence on every skeleton face.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §12.3, Theorem 12.3.1, printed p. 228 / PDF p. 270; explicit face-lattice reformulation printed p. 231 / PDF p. 273; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

namespace Grunbaum2003

/-- Grünbaum (2003), Theorem 12.3.1, printed p.228 / PDF p.270,
using the explicit equivalent face-lattice formulation on p.231 / PDF p.273.
Every given (d-2)-equivalence extends, expressing both strong and weak
 d-unambiguity. Statement only; no assertion of dimensional unambiguity. -/
theorem skeleton_equivalence_extends (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2)) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P (d - 2), Φ F.val = (φ F).val := by sorry

end Grunbaum2003
