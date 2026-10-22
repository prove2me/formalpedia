-- Prove2me | Theorems.Thm_GelfandVNA_Duality_theorem_5_19
-- name    : GelfandVNA.Duality.theorem_5_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:35.732494+00:00
-- url     : https://prove2.me/theorems/5f9215f7-63a6-4bf4-97d0-b7fad3242b96
-- title:
--   Theorem 5.19, p. 45 — ML ⊣ Spec is an adjoint equivalence CSLEMS ≃ MLoc
-- statement:
--   The functors $\mathsf{ML}\colon\mathsf{CSLEMS}\to\mathsf{MLoc}$ and $\mathrm{Spec}\colon\mathsf{MLoc}\to\mathsf{CSLEMS}$, with natural isomorphisms $\eta\colon\mathrm{id}\to\mathrm{Spec}\circ\mathsf{ML}$ and $\varepsilon\colon\mathsf{ML}\circ\mathrm{Spec}\to\mathrm{id}$, form an adjoint equivalence
--   $$\mathsf{CSLEMS}\ \simeq\ \mathsf{MLoc}.$$
--   The statement asserts an equivalence $e$ implemented by $\mathsf{ML}$: there are order isomorphisms $\iota$ from the measurable locale assigned to $(X,M,N)$ onto $M/N$, under which the image of a morphism $f$ is the pull-back $f^*\colon M'/N'\to M/N$:
--   $$\iota_{X}\big(e(f)^*\,b\big)=f^*\big(\iota_{X'}(b)\big).$$
--
--   This is the fourth equivalence of Theorem 1.1 and the point-set measure-theoretic end of the duality.
--
--   **Formalization Note** The equivalence and $\iota$ are existentially quantified; $\mathrm{Spec}$, $\eta$ and $\varepsilon$ are not named.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 45, Theorem 5.19

import Mathlib
import Definitions.Def_GelfandVNA_Duality_Locales
import Definitions.Def_GelfandVNA_Duality_EMS

namespace GelfandVNA.Duality

open CategoryTheory

universe u

/-- Theorem 5.19, p. 45: `ML : CSLEMS → MLoc` and `Spec : MLoc → CSLEMS` form an adjoint equivalence.
The functor is `ML`: it sends `(X, M, N)` to (an algebra order-isomorphic to) `M/N`, and a morphism
`f` to the map `f* : M'/N' → M/N` of frames. -/
theorem theorem_5_19 :
    ∃ e : CSLEMS.{u} ≌ MLoc.{u},
      ∃ ι : ∀ A : CSLEMS.{u}, (e.functor.obj A).carrier ≃o MmodN A.obj.E,
        ∀ {A B : CSLEMS.{u}} (f : A ⟶ B) (b : (e.functor.obj B).carrier),
          ι A (MLoc.frameHom (e.functor.map f) b) = pullHom f.hom (ι B b) := by sorry

end GelfandVNA.Duality
