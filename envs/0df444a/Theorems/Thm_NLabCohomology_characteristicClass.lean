-- Prove2me | Theorems.Thm_NLabCohomology_characteristicClass
-- name    : NLabCohomology.characteristicClass
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:45:38.24474+00:00
-- url     : https://prove2.me/theorems/93e42946-a4c9-4360-99cc-fc2ba1c76db1
-- title:
--   Characteristic classes: $[k(c)] = [X \to A \to B] \in H(X,B)$
-- statement:
--   Let $c$ be a cocycle on $X$ with coefficients in $A$, and let $k : A \to B$ be a cocycle on the coefficient object. The general definition of cohomology assigns to this data the **characteristic class** of $c$ with respect to $k$: the class of the composite cocycle
--   $$[k(c)] \coloneqq \big[\,X \xrightarrow{c} A \xrightarrow{k} B\,\big] \in H(X,B).$$
--   The "Characteristic classes" subsection states that composition of morphisms in $\mathbf{H}$ induces a map of cohomology ∞-groupoids $\mathbf{H}(X,A) \to \mathbf{H}(X,B)$ and hence a map of cohomology classes $H(X,A) \to H(X,B)$ sending each $A$-cocycle to its characteristic class.
--
--   This theorem asserts the well-definedness of that assignment: for every cocycle $k : A \to B$ there exists a map $\varphi : H(X,A) \to H(X,B)$ such that $\varphi([c]) = [k(c)]$ for every cocycle $c$ on $X$. The content is that the composite cocycle's class depends only on the class of $c$. The source's formulation for a collection of cocycles $\{c_n : A \to E_n\}$ (typically Eilenberg–MacLane objects) is the immediate corollary applied to each $c_n$.
--
--   **Formalization Note.** `charCocycle` is the composite cocycle on representatives; the theorem supplies the descended map on `Cohomology`.
-- source:
--   nLab, 'cohomology', section 3 (Definition), subsection 'General definition'; https://ncatlab.org/nlab/show/cohomology#Definition (page last revised August 11, 2026). Characteristic-class bullet of 'General definition' and subsection 'Characteristic classes'.

import Definitions.Def_NLabCohomology_Cohomology

universe u

open CategoryTheory Simplicial Opposite

namespace NLabCohomology

theorem characteristicClass (H : InfinityOneCategory.{u}) {X A B : H.Obj}
    (k : Cocycle H A B) :
    ∃ φ : Cohomology H X A → Cohomology H X B,
      ∀ c : Cocycle H X A,
        φ (cohomologyClass H c) = cohomologyClass H (charCocycle H c k) := by sorry

end NLabCohomology
