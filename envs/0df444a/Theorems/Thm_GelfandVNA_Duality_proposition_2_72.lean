-- Prove2me | Theorems.Thm_GelfandVNA_Duality_proposition_2_72
-- name    : GelfandVNA.Duality.proposition_2_72
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:12.508274+00:00
-- url     : https://prove2.me/theorems/4f45d081-6a8e-4123-865c-0bd47ea9c1a1
-- title:
--   Proposition 2.72, p. 21 — Ω ⊣ Sp restricts to an equivalence HStonean ≃ HStoneanLoc
-- statement:
--   The adjoint equivalence between Stonean spaces and Stonean locales, given by the locale of opens $\Omega$ and the space of points $\mathrm{Sp}$, restricts to an equivalence
--   $$\mathsf{HStonean}\ \simeq\ \mathsf{HStoneanLoc}$$
--   between hyperstonean spaces with open continuous maps and hyperstonean locales with open maps, implemented by $\Omega$: after forgetting to the category of all locales, the functor of the equivalence is naturally isomorphic to $S\mapsto\Omega(S)$, $f\mapsto f^{-1}$.
--
--   This is the first of the four equivalences composing Theorem 1.1.
--
--   **Formalization Note** The statement is the existence of an equivalence $e$ together with a natural isomorphism between $e$ followed by the forgetful functor to locales and Mathlib's `topToLocale` (which is $\Omega$) applied to the underlying space. The adjoint functor $\mathrm{Sp}$ is not named: an equivalence determines it up to isomorphism.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 21, Proposition 2.72

import Mathlib
import Definitions.Def_GelfandVNA_Duality_Locales
import Definitions.Def_GelfandVNA_Duality_Spaces

namespace GelfandVNA.Duality

open CategoryTheory

universe u

/-- Proposition 2.72, p. 21: the adjoint equivalence `Ω ⊣ Sp` between Stonean spaces and Stonean
locales restricts to an equivalence `HStonean ≃ HStoneanLoc`; its functor is `Ω` (Mathlib's
`topToLocale`), up to natural isomorphism after forgetting to `Loc`. -/
theorem proposition_2_72 :
    ∃ e : HStonean.{u} ≌ HStoneanLoc.{u},
      Nonempty (e.functor ⋙ HStoneanLoc.toLocale ≅ HStonean.toTopFunctor ⋙ topToLocale) := by sorry

end GelfandVNA.Duality
