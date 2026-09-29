-- Prove2me | Theorems.Thm_NeronModelInfra_existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring
-- name    : NeronModelInfra.existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/9675b7c5-9450-5b1a-8218-c36fe1264339
-- title:
--   Valuative criterion of properness over a valuation subring
-- statement:
--   Let $L$ be a field and $\mathcal O \subseteq L$ a valuation subring of $L$, and let $f : X \to Y$ be a proper morphism of schemes. Suppose given a morphism $s : \operatorname{Spec}\mathcal O \to Y$ and a morphism $x : \operatorname{Spec} L \to X$ such that the square commutes, i.e. $x$ followed by $f$ equals the morphism $\operatorname{Spec} L \to \operatorname{Spec}\mathcal O$ induced by the inclusion $\mathcal O \hookrightarrow L$ followed by $s$. The conclusion asserts that there is exactly one element $xt$ of the relative Hom-set `SchemeHomOver s f`, that is, exactly one pair consisting of a morphism $\varphi : \operatorname{Spec}\mathcal O \to X$ together with the datum that $\varphi$ followed by $f$ equals $s$, whose underlying morphism satisfies: the morphism induced by $\mathcal O \hookrightarrow L$ followed by $\varphi$ equals $x$. Uniqueness is uniqueness in the subtype, hence uniqueness of the underlying morphism $\varphi$ among morphisms over $s$ restricting to $x$.
--
--   This is the valuative criterion of properness (existence coming from universal closedness, uniqueness from separatedness), packaged so that the lift is returned as an element of the set of morphisms to $X$ over the given base point $s$, with the valuation ring presented as a valuation subring of its fraction field and the inclusion as structure map. It is used in the study of models of curves and of reduction at a place, for instance to extend an $L$-point of a proper scheme to a point over the valuation ring of a valuation of $L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring
    {L : Type u} [Field L] (O : ValuationSubring L)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (s : Spec (CommRingCat.of ↥O) ⟶ Y) (x : Spec (CommRingCat.of L) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom O.subtype) ≫ s) :
    ∃! xt : SchemeHomOver s f, Spec.map (CommRingCat.ofHom O.subtype) ≫ xt.1 = x := by sorry
