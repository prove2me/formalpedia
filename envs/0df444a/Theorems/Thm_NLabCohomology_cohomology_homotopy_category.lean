-- Prove2me | Theorems.Thm_NLabCohomology_cohomology_homotopy_category
-- name    : NLabCohomology.cohomology_homotopy_category
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:46:04.745937+00:00
-- url     : https://prove2.me/theorems/620345c3-ccb0-4be8-ab67-d18d649cd630
-- title:
--   Cohomology sets are the hom-sets of the homotopy category: $H(X,A) = \pi_0\mathbf{H}(X,A) = \mathrm{Ho}_{\mathbf{H}}(X,A)$
-- statement:
--   Let $\mathbf{H}$ be an (∞,1)-category with hom ∞-groupoids $\mathbf{H}(X,A)$, and let $H(X,A) = \pi_0\,\mathbf{H}(X,A)$ be the cohomology sets of the general definition. The nLab entry opens the definition with the identification
--   $$\pi_0\,\mathbf{H}(X,A) \;=\; \mathrm{Ho}_{\mathbf{H}}(X,A),$$
--   where $\mathrm{Ho}_{\mathbf{H}}$ is the homotopy category of $\mathbf{H}$: the cohomology sets are the hom-sets of a category whose objects are those of $\mathbf{H}$.
--
--   This theorem asserts exactly that structure: there is a composition law on cohomology classes,
--   $$H(X,Y) \times H(Y,Z) \longrightarrow H(X,Z),$$
--   such that
--
--   1. the class of the identity cocycle of $X$ is a left unit, and the class of the identity cocycle of $Y$ a right unit;
--   2. the composition is associative;
--   3. on classes of cocycles it is induced by composition of cocycles: $[c] \cdot [d] = [c \cdot d]$.
--
--   Together these say that the cohomology sets form the hom-sets of the homotopy category $\mathrm{Ho}_{\mathbf{H}}$, which is the defining identification of the general definition of cohomology. The content is the descent of composition to connected components: it must be independent of the chosen cocycle representatives.
--
--   **Formalization Note.** The homotopy category is specified by its category laws on the cohomology sets rather than by a separate construction, so the statement is the existence of the composition together with unit, associativity, and compatibility clauses.
-- source:
--   nLab, 'cohomology', section 3 (Definition), subsection 'General definition'; https://ncatlab.org/nlab/show/cohomology#Definition (page last revised August 11, 2026). Opening paragraph of 'General definition': π₀𝐇(X,A) = Ho_𝐇(X,A).

import Definitions.Def_NLabCohomology_Cohomology

universe u

open CategoryTheory Simplicial Opposite

namespace NLabCohomology

theorem cohomology_homotopy_category (H : InfinityOneCategory.{u}) :
    ∃ comp : ∀ (X Y Z : H.Obj), Cohomology H X Y → Cohomology H Y Z → Cohomology H X Z,
      (∀ (X Y : H.Obj) (f : Cohomology H X Y),
        comp X X Y (cohomologyClass H (H.id X)) f = f) ∧
      (∀ (X Y : H.Obj) (f : Cohomology H X Y),
        comp X Y Y f (cohomologyClass H (H.id Y)) = f) ∧
      (∀ (W X Y Z : H.Obj) (f : Cohomology H W X) (g : Cohomology H X Y)
        (h : Cohomology H Y Z),
        comp W Y Z (comp W X Y f g) h = comp W X Z f (comp X Y Z g h)) ∧
      (∀ (X Y Z : H.Obj) (c : Cocycle H X Y) (d : Cocycle H Y Z),
        comp X Y Z (cohomologyClass H c) (cohomologyClass H d) =
          cohomologyClass H (H.comp c d)) := by sorry

end NLabCohomology
