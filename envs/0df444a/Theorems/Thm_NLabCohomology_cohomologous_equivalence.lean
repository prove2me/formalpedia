-- Prove2me | Theorems.Thm_NLabCohomology_cohomologous_equivalence
-- name    : NLabCohomology.cohomologous_equivalence
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:45:24.534422+00:00
-- url     : https://prove2.me/theorems/2b287c34-cfbb-445b-a4a6-ece42d3b4863
-- title:
--   Cohomologous cocycles form equivalence classes
-- statement:
--   In the general definition of cohomology, the cohomology classes are introduced as the *equivalence classes* of cohomologous cocycles: two cocycles $c_1, c_2$ on $X$ with coefficients in $A$ are **cohomologous** when they are connected by a coboundary, i.e. by a morphism $\lambda : c_1 \to c_2$ in the hom ∞-groupoid $\mathbf{H}(X,A)$.
--
--   This theorem makes the presupposed fact explicit: for every (∞,1)-category $\mathbf{H}$ and all objects $X, A$, the relation of being cohomologous is an **equivalence relation** on the type of cocycles on $X$ with coefficients in $A$ — reflexive, symmetric, and transitive. It is what justifies speaking of the equivalence class $[c] \in \pi_0\,\mathbf{H}(X,A)$ of a cocycle and of the cohomology set as the set of these classes.
--
--   **Formalization Note.** The relation is `SSet.π₀Rel` (existence of an edge) on the hom Kan complex; the Kan horn-filling condition is available from the `InfinityOneCategory` structure.
-- source:
--   nLab, 'cohomology', section 3 (Definition), subsection 'General definition'; https://ncatlab.org/nlab/show/cohomology#Definition (page last revised August 11, 2026). Bullets on coboundaries/cohomologous cocycles and cohomology classes.

import Definitions.Def_NLabCohomology_Cohomology

universe u

open CategoryTheory Simplicial Opposite

namespace NLabCohomology

theorem cohomologous_equivalence (H : InfinityOneCategory.{u}) (X A : H.Obj) :
    Equivalence (fun c₁ c₂ : Cocycle H X A => Cohomologous H c₁ c₂) := by sorry

end NLabCohomology
