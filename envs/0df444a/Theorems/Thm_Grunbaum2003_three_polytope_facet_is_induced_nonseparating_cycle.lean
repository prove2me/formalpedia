-- Prove2me | Theorems.Thm_Grunbaum2003_three_polytope_facet_is_induced_nonseparating_cycle
-- name    : Grunbaum2003.three_polytope_facet_is_induced_nonseparating_cycle
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T23:40:13.862819+00:00
-- url     : https://prove2.me/theorems/d8855170-7e83-4fab-a90f-8aae9a438481
-- title:
--   Every facet of a 3-polytope induces a 2-regular connected nonseparating down-set in the 1-skeleton
-- statement:
--   Let $P \subseteq \mathbb{R}^3$ be a $3$-polytope (`IsDPolytope P`) and let $F$ be a facet of $P$ ($\dim F = 2$). Let $\mathcal{L}_1 = \operatorname{skel}_1(P)$ be the $1$-skeleton poset of $P$, with poset-intrinsic predicates for the bottom element ($\operatorname{isBot}$), atoms/vertices ($\operatorname{isAtom}$), and maximal elements/edges ($\operatorname{isEdge}$). Then the facet down-set $\mathcal{C} = \{S \in \mathcal{L}_1 : S \subseteq F\}$ satisfies:
--
--   1. (**Atom-induced**) $S \in \mathcal{C}$ if and only if every atom $A \le S$ belongs to $\mathcal{C}$;
--   2. (**Nonempty and $2$-regular**) $\mathcal{C}$ contains at least one atom, and every atom $A \in \mathcal{C}$ is contained in exactly two distinct edges $E_1 \ne E_2$ in $\mathcal{C}$;
--   3. (**Connected**) Every nonempty subset of atoms of $\mathcal{C}$ closed under edges of $\mathcal{C}$ contains all atoms of $\mathcal{C}$;
--   4. (**Nonseparating**) There exists an atom outside $\mathcal{C}$, and every nonempty subset of atoms outside $\mathcal{C}$ closed under edges with both endpoints outside $\mathcal{C}$ contains all atoms outside $\mathcal{C}$.
--
--   **Formalization Note** Polytopes are represented by `IsDPolytope`, exposed faces by `PolytopeFace`, and the $1$-skeleton by `SkeletonFace P 1`.
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

theorem three_polytope_facet_is_induced_nonseparating_cycle
    (P : Set (Fin 3 → ℝ)) (hP : IsDPolytope P)
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = 2) :
    let isBot : SkeletonFace P 1 → Prop := fun B => ∀ X : SkeletonFace P 1, B ≤ X
    let isAtom : SkeletonFace P 1 → Prop := fun A =>
      ¬ isBot A ∧ ∀ X : SkeletonFace P 1, X < A → isBot X
    let isEdge : SkeletonFace P 1 → Prop := fun E =>
      ∀ X : SkeletonFace P 1, E ≤ X → X = E
    let C : Set (SkeletonFace P 1) := {S : SkeletonFace P 1 | S.val ≤ F}
    (∀ S : SkeletonFace P 1, S ∈ C ↔ (∀ A : SkeletonFace P 1, isAtom A → A ≤ S → A ∈ C)) ∧
    ((∃ A : SkeletonFace P 1, isAtom A ∧ A ∈ C) ∧
      ∀ A : SkeletonFace P 1, isAtom A → A ∈ C →
        ∃ E₁ E₂ : SkeletonFace P 1,
          isEdge E₁ ∧ isEdge E₂ ∧ E₁ ∈ C ∧ E₂ ∈ C ∧ E₁ ≠ E₂ ∧ A ≤ E₁ ∧ A ≤ E₂ ∧
          ∀ E : SkeletonFace P 1, isEdge E → E ∈ C → A ≤ E → E = E₁ ∨ E = E₂) ∧
    (∀ (Good : SkeletonFace P 1 → Prop),
      (∃ A₀ : SkeletonFace P 1, isAtom A₀ ∧ A₀ ∈ C ∧ Good A₀) →
      (∀ A B E : SkeletonFace P 1, isAtom A → isAtom B → isEdge E →
        A ∈ C → B ∈ C → E ∈ C → A ≤ E → B ≤ E → Good A → Good B) →
      ∀ A : SkeletonFace P 1, isAtom A → A ∈ C → Good A) ∧
    ((∃ W : SkeletonFace P 1, isAtom W ∧ W ∉ C) ∧
      ∀ (Good : SkeletonFace P 1 → Prop),
        (∃ W₀ : SkeletonFace P 1, isAtom W₀ ∧ W₀ ∉ C ∧ Good W₀) →
        (∀ U V E : SkeletonFace P 1, isAtom U → isAtom V → isEdge E →
          U ∉ C → V ∉ C → U ≤ E → V ≤ E → Good U → Good V) →
        ∀ W : SkeletonFace P 1, isAtom W → W ∉ C → Good W) := by sorry

end Grunbaum2003
