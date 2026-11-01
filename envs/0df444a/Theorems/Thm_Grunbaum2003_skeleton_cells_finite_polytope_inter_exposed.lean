-- Prove2me | Theorems.Thm_Grunbaum2003_skeleton_cells_finite_polytope_inter_exposed
-- name    : Grunbaum2003.skeleton_cells_finite_polytope_inter_exposed
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:33.345492+00:00
-- url     : https://prove2.me/theorems/99e68791-7b15-4ad7-b40a-5d2475c8a1a5
-- title:
--   Ambient realizability and cell-poset structure of the $k$-skeleton of a $d$-polytope
-- statement:
--   This theorem establishes the ambient-space realizability and polytopal-complex cell properties of the $k$-skeleton $\operatorname{skel}_k(P)$ of a $d$-polytope $P \subseteq \mathbb{R}^d$.
--
--   Let $d, k \in \mathbb{N}$ and let $P \subseteq \mathbb{R}^d$ be a $d$-polytope (`IsDPolytope P`). Let
--
--   $$
--   \mathcal{C}_k(P) = \bigl\{ F \subseteq \mathbb{R}^d \;\big|\; F \in \operatorname{skel}_k(P) \bigr\}
--   $$
--
--   denote the collection of underlying subsets in $\mathbb{R}^d$ of all faces in the $k$-skeleton of $P$, and let $|\operatorname{skel}_k(P)| = \bigcup_{F \in \operatorname{skel}_k(P)} F$ denote the skeleton carrier (`skeletonCarrier P k`). Then:
--
--   1. There exists a subset $S \subseteq \mathbb{R}^d$ homeomorphic to $|\operatorname{skel}_k(P)|$;
--   2. The family $\mathcal{C}_k(P)$ is finite;
--   3. Every cell $F \in \mathcal{C}_k(P)$ is either empty ($F = \emptyset$) or a polytope (`IsPolytope F`);
--   4. For every pair of cells $F, G \in \mathcal{C}_k(P)$, the intersection $F \cap G$ is an exposed face of both $F$ and $G$:
--
--   $$
--   \forall F, G \in \mathcal{C}_k(P),\quad \operatorname{IsExposed}_{\mathbb{R}}(F, F \cap G) \;\land\; \operatorname{IsExposed}_{\mathbb{R}}(G, F \cap G);
--   $$
--
--   5. The abstract $k$-skeleton poset `SkeletonFace P k` is order-isomorphic to $\mathcal{C}_k(P)$ ordered by inclusion.
--
--   These five properties verify the topological embedding at $m = d$ and all structural components of `IsPolytopalComplex` for the canonical ambient realization $\mathcal{C}_k(P) \subseteq \mathcal{P}(\mathbb{R}^d)$ in Grünbaum's §11.1 (`skeleton_embedding_dimension`).
--
--   **Formalization Note** Finiteness and polytopality of each cell $F \in \mathcal{C}_k(P)$ follow from the vertex-hull representation $F = \operatorname{conv}(F \cap \operatorname{vert}(P))$, while exposedness of $F \cap G$ in $F$ follows by restricting the linear functional that exposes $G$ in $P$ to $F$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §11.1, pp. 199–204, Theorem 11.1.9

import Definitions.Def_Grunbaum2003_IsPolytope
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_skeletonCarrier
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Order.Hom.Basic

set_option autoImplicit false

namespace Grunbaum2003

theorem skeleton_cells_finite_polytope_inter_exposed (d k : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    (∃ S : Set (Fin d → ℝ), Nonempty ((skeletonCarrier P k) ≃ₜ S)) ∧
    (Set.range (fun F : SkeletonFace P k => F.val.val)).Finite ∧
    (∀ F ∈ Set.range (fun F : SkeletonFace P k => F.val.val), F = ∅ ∨ IsPolytope F) ∧
    (∀ F ∈ Set.range (fun F : SkeletonFace P k => F.val.val),
      ∀ G ∈ Set.range (fun F : SkeletonFace P k => F.val.val),
        IsExposed ℝ F (F ∩ G) ∧ IsExposed ℝ G (F ∩ G)) ∧
    Nonempty (SkeletonFace P k ≃o Set.range (fun F : SkeletonFace P k => F.val.val)) := by sorry

end Grunbaum2003
