-- Prove2me | Theorems.Thm_Grunbaum2003_skeleton_embedding_dimension
-- name    : Grunbaum2003.skeleton_embedding_dimension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:40:26.710453+00:00
-- url     : https://prove2.me/theorems/955d2286-bcbf-4e08-81e2-e79031dea497
-- title:
--   Theorem 11.1.9 — Exact embedding dimensions of polytope skeletons
-- statement:
--   For every d-polytope P and 1 ≤ k ≤ d, the least Euclidean dimension admitting a topological embedding of its k-skeleton and the least dimension admitting a combinatorially equivalent finite polytopal complex are both the explicit value a(d,k)=b(d,k).
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §11.1, Theorem 11.1.9, printed pp. 204–205 / PDF pp. 244–245; definitions printed pp. 199–202 / PDF pp. 239–242; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_skeletonCarrier
import Definitions.Def_Grunbaum2003_IsPolytopalComplex
import Definitions.Def_Grunbaum2003_skeletonEmbeddingDimension
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Order.Bounds.Defs

set_option autoImplicit false

namespace Grunbaum2003

/-- Grünbaum (2003), §11.1, Theorem 9 (11.1.9), printed p.204 / PDF244:
b(skel_k P)=a(skel_k P)=a(d,k)=b(d,k). The source scope 1≤k≤d is
specified on p.201. The common value is made explicit using 11.1.4.

`IsLeast` expresses both realizability at the claimed dimension and the
lower bound for every possible ambient dimension. The first set uses
homeomorphisms onto arbitrary subsets, with their subspace topology.
The second uses genuine finite polytopal complexes and an order isomorphism
of the full cell posets, not merely a subdivision or topological equivalence.
P is arbitrary (including simplices), so the simplex comparison is retained.
Statement only; no proof lemmas. -/
theorem skeleton_embedding_dimension (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    IsLeast {m : ℕ | ∃ S : Set (Fin m → ℝ),
      Nonempty ((skeletonCarrier P k) ≃ₜ S)}
      (skeletonEmbeddingDimension d k) ∧
    IsLeast {m : ℕ | ∃ C : Set (Set (Fin m → ℝ)),
      IsPolytopalComplex C ∧ Nonempty (SkeletonFace P k ≃o C)}
      (skeletonEmbeddingDimension d k) := by sorry

end Grunbaum2003
