-- Prove2me | Theorems.Thm_GoodReductionJacobian_PartialAction_closure_image_preimage_closure_eq_closure_singleton
-- name    : GoodReductionJacobian.PartialAction.closure_image_preimage_closure_eq_closure_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/fbc9aa8b-e42d-56d5-afc6-1794e187e785
-- title:
--   Closure of a partial-action image equals closure of image of generic point
-- statement:
--   Let $k$ be a field, let $f : G \to \operatorname{Spec} k$ and $p : P \to \operatorname{Spec} k$ be morphisms of schemes, and let $a$ be a partial action datum of $f$ on $p$, i.e. the data of an open subscheme $\operatorname{dom} a$ of the fibre product $G \times_{\operatorname{Spec} k} P$ which is dense as a subset, a morphism $a.\mathrm{hom} : \operatorname{dom} a \to P$, and the identity $a.\mathrm{hom} \cdot p = \iota \cdot \mathrm{pr}_2 \cdot p$ (composites in diagrammatic order, $\iota$ the open immersion of $\operatorname{dom} a$ and $\mathrm{pr}_2$ the second projection). Let $Z$ be an arbitrary subset of the underlying topological space of $P$ and let $\zeta$ be a point of $G \times_{\operatorname{Spec} k} P$ lying in $\operatorname{dom} a$, and assume that the closure of $\{\zeta\}$ equals the preimage $\mathrm{pr}_2^{-1}(\overline{Z})$ of the closure of $Z$ under the second projection. Then, on underlying spaces, the closure of the image under $a.\mathrm{hom}$ of the set $(\iota \cdot \mathrm{pr}_2)^{-1}(\overline{Z}) \subseteq \operatorname{dom} a$ coincides with the closure in $P$ of the single point $a.\mathrm{hom}(\zeta)$.
--
--   This is a purely topological step in the construction of group actions on Néron models by Rosenlicht's method: the locus swept out of $G \times_k \overline{Z}$ by a partially defined action has the same closure as the orbit of the generic point $\zeta$ of $G \times_k \overline{Z}$. It is used by [`GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one`](thm.html#GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one), where such closures are compared via dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_PartialAction_closure_image_preimage_closure_eq_closure_singleton.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.PartialAction.closure_image_preimage_closure_eq_closure_singleton
    {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} (a : PartialAction k f p)
    (Z : Set ↥P) (ζ : ↥(pullback f p)) (hζ : ζ ∈ a.dom)
    (hζcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure Z) :
    closure (a.hom.base '' ((a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure Z)) =
      closure ({a.hom.base ⟨ζ, hζ⟩} : Set ↥P) := by sorry
