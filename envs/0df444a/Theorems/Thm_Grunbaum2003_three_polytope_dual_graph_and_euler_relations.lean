-- Prove2me | Theorems.Thm_Grunbaum2003_three_polytope_dual_graph_and_euler_relations
-- name    : Grunbaum2003.three_polytope_dual_graph_and_euler_relations
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T00:05:19.515116+00:00
-- url     : https://prove2.me/theorems/ca4cf113-08ce-480e-8377-7ce26f02b1c8
-- title:
--   Facet finiteness, ridge-facet diamond property, dual connectivity, and Euler's relation for general 3-polytopes
-- statement:
--   Let $Q \subseteq \mathbb{R}^3$ be a convex $3$-polytope (`IsDPolytope Q`). Then the atoms $\mathcal{A}$ (vertices), maximal elements $\mathcal{E}$ (edges) of the $1$-skeleton poset $\operatorname{skel}_1(Q)$, and facets $\mathcal{F}$ ($2$-dimensional exposed faces in $\operatorname{PolytopeFace} Q$) form finite sets (`Finset`) satisfying:
--
--   1. **Diamond property at ridges:** Every edge $E \in \mathcal{E}$ is contained in exactly two distinct facets $F_1, F_2 \in \mathcal{F}$;
--   2. **Dual graph connectivity:** Any nonempty subset of $\mathcal{F}$ that is closed under sharing an edge $E \in \mathcal{E}$ equals all of $\mathcal{F}$;
--   3. **Euler's formula for $3$-polytopes:** $|\mathcal{A}| + |\mathcal{F}| = |\mathcal{E}| + 2$.
--
--   **Formalization Note** Polytopes are represented by `IsDPolytope`, exposed faces by `PolytopeFace`, and the $1$-skeleton by `SkeletonFace Q 1`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §8.1 (Euler's theorem, p. 130) and §11.3

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false
open Classical

namespace Grunbaum2003

theorem three_polytope_dual_graph_and_euler_relations
    (Q : Set (Fin 3 → ℝ)) (hQ : IsDPolytope Q) :
    let isBot : SkeletonFace Q 1 → Prop := fun B => ∀ X : SkeletonFace Q 1, B ≤ X
    let isAtom : SkeletonFace Q 1 → Prop := fun A =>
      ¬ isBot A ∧ ∀ X : SkeletonFace Q 1, X < A → isBot X
    let isEdge : SkeletonFace Q 1 → Prop := fun E =>
      ∀ X : SkeletonFace Q 1, E ≤ X → X = E
    let isFacet : PolytopeFace Q → Prop := fun F =>
      F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2
    ∃ (𝒜 ℰ : Finset (SkeletonFace Q 1)) (ℱ : Finset (PolytopeFace Q)),
      (∀ A : SkeletonFace Q 1, A ∈ 𝒜 ↔ isAtom A) ∧
      (∀ E : SkeletonFace Q 1, E ∈ ℰ ↔ isEdge E) ∧
      (∀ F : PolytopeFace Q, F ∈ ℱ ↔ isFacet F) ∧
      (∀ E ∈ ℰ, ∃ F₁ ∈ ℱ, ∃ F₂ ∈ ℱ, F₁ ≠ F₂ ∧ E.val ≤ F₁ ∧ E.val ≤ F₂ ∧
        ∀ F ∈ ℱ, E.val ≤ F → F = F₁ ∨ F = F₂) ∧
      (∀ (GoodF : PolytopeFace Q → Prop),
        (∃ F₀ ∈ ℱ, GoodF F₀) →
        (∀ F₁ ∈ ℱ, ∀ F₂ ∈ ℱ, ∀ E ∈ ℰ, E.val ≤ F₁ → E.val ≤ F₂ → GoodF F₁ → GoodF F₂) →
        ∀ F ∈ ℱ, GoodF F) ∧
      𝒜.card + ℱ.card = ℰ.card + 2 := by sorry

end Grunbaum2003
