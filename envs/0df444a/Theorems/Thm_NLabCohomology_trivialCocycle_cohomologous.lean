-- Prove2me | Theorems.Thm_NLabCohomology_trivialCocycle_cohomologous
-- name    : NLabCohomology.trivialCocycle_cohomologous
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:45:53.721572+00:00
-- url     : https://prove2.me/theorems/72d70fb4-8a82-4ae5-a62b-be2478bcd231
-- title:
--   The trivial cocycle is canonical up to coboundary
-- statement:
--   In the general definition of cohomology, when the coefficient object $A$ is pointed by a morphism $* \to A$ from the terminal object $*$ of $\mathbf{H}$, the composite $X \to * \to A$ is called *the* **trivial cocycle** $c_{\mathrm{triv}}$ on $X$. The definite article presupposes that the trivial cocycle is canonical up to coboundary: the morphism $X \to *$ is unique up to homotopy because $\mathbf{H}(X,*)$ is contractible.
--
--   This theorem asserts exactly that: for a terminal object $*$ of $\mathbf{H}$ and any object $X$, any two cocycles $t_1, t_2 : X \to *$ are cohomologous. Consequently the cohomology class of the trivial cocycle does not depend on the choice of cocycle $X \to *$ used to define it.
--
--   **Formalization Note.** Contractibility of $\mathbf{H}(X,*)$ is part of the `TerminalObject` structure (boundary-extension form); the theorem converts it into connectedness of the space of cocycles into $*$.
-- source:
--   nLab, 'cohomology', section 3 (Definition), subsection 'General definition'; https://ncatlab.org/nlab/show/cohomology#Definition (page last revised August 11, 2026). Trivial-cocycle bullet of 'General definition'.

import Definitions.Def_NLabCohomology_Cohomology

universe u

open CategoryTheory Simplicial Opposite

namespace NLabCohomology

theorem trivialCocycle_cohomologous (H : InfinityOneCategory.{u})
    (T : TerminalObject H) (X : H.Obj) (t₁ t₂ : Cocycle H X T.star) :
    Cohomologous H t₁ t₂ := by sorry

end NLabCohomology
