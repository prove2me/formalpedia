-- Prove2me | Theorems.Thm_Grunbaum2003_skeletonEmbeddingDimension_realizable_and_lower_bounds
-- name    : Grunbaum2003.skeletonEmbeddingDimension_realizable_and_lower_bounds
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:50.298986+00:00
-- url     : https://prove2.me/theorems/a49ed2fc-4adf-4587-9a1b-239a300cb08f
-- title:
--   Realizability and Van Kampen–Flores lower bounds at `skeletonEmbeddingDimension d k`
-- statement:
--   This lemma states Grünbaum's Theorem 11.1.9 (together with Theorem 11.1.4 and the Van Kampen–Flores topological non-embeddability theorem): given the ambient $d$-dimensional properties of the $k$-skeleton cell family $\mathcal{C}_k(P)$ established in `skeleton_cells_finite_polytope_inter_exposed`, the common topological and polytopal embedding dimension of $\operatorname{skel}_k(P)$ for any $d$-polytope $P$ ($1 \le k \le d$) is `skeletonEmbeddingDimension d k`.
--
--   Let $1 \le k \le d$, let $P \subseteq \mathbb{R}^d$ be a $d$-polytope (`IsDPolytope P`), and write
--
--   $$
--   a(d, k) = b(d, k) = \begin{cases} d & \text{if } d \le k + 1, \\ \min(d - 1, 2k + 1) & \text{if } d \ge k + 2 \end{cases}
--   $$
--
--   for `skeletonEmbeddingDimension d k`. Given the ambient cell-poset package `hAmb` for $\mathcal{C}_k(P) = \{F \subseteq \mathbb{R}^d \mid F \in \operatorname{skel}_k(P)\}$, the integer $a(d, k)$ is the least element (`IsLeast`) of both:
--
--   1. The set of dimensions $m \in \mathbb{N}$ in which the carrier $|\operatorname{skel}_k(P)|$ embeds topologically (`∃ S : Set (Fin m → ℝ), Nonempty (skeletonCarrier P k ≃ₜ S)`); and
--   2. The set of dimensions $m \in \mathbb{N}$ in which $\operatorname{skel}_k(P)$ is realized as the cell poset of a finite polytopal complex (`∃ C : Set (Set (Fin m → ℝ)), IsPolytopalComplex C ∧ Nonempty (SkeletonFace P k ≃o C)`).
--
--   Combining this lemma with `skeleton_cells_finite_polytope_inter_exposed` immediately proves `skeleton_embedding_dimension`.
--
--   **Formalization Note** For $d \le k + 1$, $a(d, k) = d$ is realized directly in the ambient space $\mathbb{R}^d$; for $d \ge k + 2$, upper bounds use Schlegel projection into $\mathbb{R}^{d-1}$ and generic projection into $\mathbb{R}^{2k+1}$, while lower bounds follow from boundary refinement of the $d$-simplex (`boundary_refines_simplex`) and the Van Kampen–Flores theorem.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §11.1, pp. 201–204, Theorems 11.1.4 & 11.1.9

import Definitions.Def_Grunbaum2003_IsPolytope
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_skeletonCarrier
import Definitions.Def_Grunbaum2003_IsPolytopalComplex
import Definitions.Def_Grunbaum2003_skeletonEmbeddingDimension
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Order.Bounds.Defs

set_option autoImplicit false

namespace Grunbaum2003

theorem skeletonEmbeddingDimension_realizable_and_lower_bounds (d k : ℕ)
    (hk : 1 ≤ k) (hkd : k ≤ d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hAmb :
      (∃ S : Set (Fin d → ℝ), Nonempty ((skeletonCarrier P k) ≃ₜ S)) ∧
      (Set.range (fun F : SkeletonFace P k => F.val.val)).Finite ∧
      (∀ F ∈ Set.range (fun F : SkeletonFace P k => F.val.val), F = ∅ ∨ IsPolytope F) ∧
      (∀ F ∈ Set.range (fun F : SkeletonFace P k => F.val.val),
        ∀ G ∈ Set.range (fun F : SkeletonFace P k => F.val.val),
          IsExposed ℝ F (F ∩ G) ∧ IsExposed ℝ G (F ∩ G)) ∧
      Nonempty (SkeletonFace P k ≃o Set.range (fun F : SkeletonFace P k => F.val.val))) :
    IsLeast {m : ℕ | ∃ S : Set (Fin m → ℝ),
      Nonempty ((skeletonCarrier P k) ≃ₜ S)}
      (skeletonEmbeddingDimension d k) ∧
    IsLeast {m : ℕ | ∃ C : Set (Set (Fin m → ℝ)),
      IsPolytopalComplex C ∧ Nonempty (SkeletonFace P k ≃o C)}
      (skeletonEmbeddingDimension d k) := by sorry

end Grunbaum2003
