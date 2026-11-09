-- Prove2me | Theorems.Thm_Grunbaum2003_three_polytope_facet_of_induced_nonseparating_cycle
-- name    : Grunbaum2003.three_polytope_facet_of_induced_nonseparating_cycle
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T23:40:04.625443+00:00
-- url     : https://prove2.me/theorems/ce4e92c2-37d5-4ebb-9a11-c5c19cd153a2
-- title:
--   Every induced nonseparating 2-regular connected cycle in the 1-skeleton of a 3-polytope is a facet down-set
-- statement:
--   Let $Q \subseteq \mathbb{R}^3$ be a $3$-polytope (`IsDPolytope Q`) and let $\mathcal{C} \subseteq \operatorname{skel}_1(Q)$ be a subset of the $1$-skeleton poset that is atom-induced, nonempty and $2$-regular on atoms and edges, connected along edges in $\mathcal{C}$, and nonseparating (its complement on atoms is nonempty and connected along outside edges). Then there exists an exposed face $G$ of $Q$ whose down-set in $\operatorname{skel}_1(Q)$ is $\mathcal{C}$:
--
--   $$\forall T \in \operatorname{skel}_1(Q), \qquad T \subseteq G \iff T \in \mathcal{C}.$$
--
--   **Formalization Note** Polytopes are represented by `IsDPolytope`, exposed faces by `PolytopeFace`, and the $1$-skeleton by `SkeletonFace Q 1`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §11.3 and §12.3, Theorem 12.3.1, printed p. 228 / PDF p. 270; Guillermo Pineda-Villavicencio, Julien Ugon, and David Yost, Reconstructing Polytopes and Pseudomanifolds, arXiv:2503.16807, §1

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem three_polytope_facet_of_induced_nonseparating_cycle
    (Q : Set (Fin 3 → ℝ)) (hQ : IsDPolytope Q)
    (C : Set (SkeletonFace Q 1)) :
    let isBot : SkeletonFace Q 1 → Prop := fun B => ∀ X : SkeletonFace Q 1, B ≤ X
    let isAtom : SkeletonFace Q 1 → Prop := fun A =>
      ¬ isBot A ∧ ∀ X : SkeletonFace Q 1, X < A → isBot X
    let isEdge : SkeletonFace Q 1 → Prop := fun E =>
      ∀ X : SkeletonFace Q 1, E ≤ X → X = E
    (∀ S : SkeletonFace Q 1, S ∈ C ↔ (∀ A : SkeletonFace Q 1, isAtom A → A ≤ S → A ∈ C)) →
    ((∃ A : SkeletonFace Q 1, isAtom A ∧ A ∈ C) ∧
      ∀ A : SkeletonFace Q 1, isAtom A → A ∈ C →
        ∃ E₁ E₂ : SkeletonFace Q 1,
          isEdge E₁ ∧ isEdge E₂ ∧ E₁ ∈ C ∧ E₂ ∈ C ∧ E₁ ≠ E₂ ∧ A ≤ E₁ ∧ A ≤ E₂ ∧
          ∀ E : SkeletonFace Q 1, isEdge E → E ∈ C → A ≤ E → E = E₁ ∨ E = E₂) →
    (∀ (Good : SkeletonFace Q 1 → Prop),
      (∃ A₀ : SkeletonFace Q 1, isAtom A₀ ∧ A₀ ∈ C ∧ Good A₀) →
      (∀ A B E : SkeletonFace Q 1, isAtom A → isAtom B → isEdge E →
        A ∈ C → B ∈ C → E ∈ C → A ≤ E → B ≤ E → Good A → Good B) →
      ∀ A : SkeletonFace Q 1, isAtom A → A ∈ C → Good A) →
    ((∃ W : SkeletonFace Q 1, isAtom W ∧ W ∉ C) ∧
      ∀ (Good : SkeletonFace Q 1 → Prop),
        (∃ W₀ : SkeletonFace Q 1, isAtom W₀ ∧ W₀ ∉ C ∧ Good W₀) →
        (∀ U V E : SkeletonFace Q 1, isAtom U → isAtom V → isEdge E →
          U ∉ C → V ∉ C → U ≤ E → V ≤ E → Good U → Good V) →
        ∀ W : SkeletonFace Q 1, isAtom W → W ∉ C → Good W) →
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q 1, T.val ≤ G ↔ T ∈ C := by sorry

end Grunbaum2003
