-- Prove2me | Theorems.Thm_GelfandVNA_Duality_proposition_2_73
-- name    : GelfandVNA.Duality.proposition_2_73
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:09.714175+00:00
-- url     : https://prove2.me/theorems/9ab822c1-d760-4723-b288-b34c529a2882
-- title:
--   Proposition 2.73, p. 22 — hyperstonean duality: COpen ⊣ Ideal restricts to HStoneanLoc ≃ LBAlg^op = MLoc
-- statement:
--   **Hyperstonean duality.** The adjoint equivalence between Stonean locales and complete Boolean algebras, given by compact opens $\mathrm{COpen}$ and the ideal locale $\mathrm{Ideal}$, restricts to an equivalence
--   $$\mathsf{HStoneanLoc}\ \simeq\ \mathsf{LBAlg}^{\mathrm{op}}=\mathsf{MLoc}$$
--   between hyperstonean locales and measurable locales, implemented by $\mathrm{COpen}$: there are order isomorphisms $\iota_L$ from the measurable locale assigned to $L$ onto the poset of compact opens of $L$, under which the image of an open map $f\colon L\to L'$ (frame map $f^*\colon L'\to L$) is the restriction of $f^*$ to compact opens:
--   $$\iota_L\big(e(f)^*\,b\big)=f^*\big(\iota_{L'}(b)\big)\quad\text{for all opens } b \text{ of } e(L').$$
--
--   This is the second equivalence of Theorem 1.1.
--
--   **Formalization Note** The equivalence is existentially quantified, together with the family $\iota$ and its compatibility with morphisms; $\mathrm{Ideal}$ is not named. Compact opens are the compact elements (`IsCompactElement`) of the frame.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 22, Proposition 2.73

import Mathlib
import Definitions.Def_GelfandVNA_Duality_Locales

namespace GelfandVNA.Duality

open CategoryTheory

universe u

/-- Proposition 2.73, p. 22 (hyperstonean duality): the adjoint equivalence `COpen ⊣ Ideal` between
Stonean locales and `CBAlg^op` restricts to an equivalence `HStoneanLoc ≃ LBAlg^op = MLoc`. Its
functor is `COpen`: it sends `L` to (an algebra order-isomorphic to) the compact opens of `L`, and an
open map of locales to the restriction of its frame map to compact opens. -/
theorem proposition_2_73 :
    ∃ e : HStoneanLoc.{u} ≌ MLoc.{u},
      ∃ ι : ∀ L : HStoneanLoc.{u}, (e.functor.obj L).carrier ≃o
          {a : L.carrier // IsCompactElement a},
        ∀ {L L' : HStoneanLoc.{u}} (f : L ⟶ L') (b : (e.functor.obj L').carrier),
          ((ι L (MLoc.frameHom (e.functor.map f) b) : L.carrier)) =
            f.1 ((ι L' b : L'.carrier)) := by sorry

end GelfandVNA.Duality
