-- Prove2me | Theorems.Thm_GelfandVNA_Duality_proposition_4_54
-- name    : GelfandVNA.Duality.proposition_4_54
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:20.202923+00:00
-- url     : https://prove2.me/theorems/53ce99f4-4fd8-46c5-a86d-642341f90ca8
-- title:
--   Proposition 4.54, p. 36 — strictly localizable enhanced measurable spaces are localizable
-- statement:
--   Let $(X,M,N)$ be a strictly localizable enhanced measurable space: isomorphic, through premaps, to a coproduct of a small family of σ-finite enhanced measurable spaces. Then $(X,M,N)$ is **localizable** (Definition 4.34): the Boolean algebra
--   $$M/N$$
--   of measurable sets modulo negligible sets is a localizable Boolean algebra, i.e. it is complete and $1$ is the supremum of the elements $a$ for which $a\,(M/N)$ admits a finite faithful continuous valuation.
--
--   This is the step that sends the objects of CSLEMS to measurable locales under $\mathsf{ML}$.
--
--   **Formalization Note** $M/N$ carries only its quotient order in the definitions; the statement provides a complete Boolean algebra order-isomorphic to it that satisfies `HasFiniteValuationCover`.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 36, Proposition 4.54 (with Definition 4.34)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_EMS

namespace GelfandVNA.Duality

open QAlgorithms.Papers.Independent.Support21.P20

universe u

/-- Proposition 4.54, p. 36: strictly localizable enhanced measurable spaces are localizable
(Definition 4.34): `M/N` is a localizable Boolean algebra. -/
theorem proposition_4_54 {X : Type u} (E : Enhanced X) (hE : IsStrictlyLocalizable E) :
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
      HasFiniteValuationCover B ∧ Nonempty (MmodN E ≃o B) := by sorry

end GelfandVNA.Duality
