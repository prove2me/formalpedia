-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/d6cd8ef9-6e74-5a50-8118-616ebd59feff
-- title:
--   Surjective homomorphism with finite kernel is finite and flat
-- statement:
--   Let $K$ be a field, let $f_X : X \to \operatorname{Spec} K$ and $f_Y : Y \to \operatorname{Spec} K$ be morphisms of schemes, and let $L_X$, $L_Y$ be relative group laws on $f_X$, $f_Y$: for every $K$-scheme $t : T \to \operatorname{Spec} K$ a multiplication, unit and inverse on the set of $T$-points $\{\varphi : T \to X \mid \varphi \circ f_X = t\}$ (resp. for $Y$) satisfying associativity, the two unit laws, left inversion, and compatibility with precomposition along any $\psi : T' \to T$ over $\operatorname{Spec} K$. Both laws are assumed commutative, and both $f_X$, $f_Y$ are assumed to satisfy `AbelianSchemePropertyBundle`: smooth, proper, with $f^{-1}(\{s\})$ connected for every point $s$ of $\operatorname{Spec} K$, and admitting some relative group law. Let $u : X \to Y$ satisfy $u \circ f_Y = f_X$, and assume $u$ is a homomorphism on points: for all $T$ over $K$ and all $T$-points $x,y$ of $X$, composing $L_X$-multiplication with $u$ agrees with the $L_Y$-product of $x \circ u$ and $y \circ u$. Assume further that $u$ is surjective on underlying spaces and that the projection to $\operatorname{Spec} K$ of the fibre product of $u$ with the unit section $\operatorname{Spec} K \to Y$ of $L_Y$ is a finite morphism. Then $u$ is finite and flat.
--
--   This is the standard statement that an isogeny of abelian varieties — a surjective homomorphism with finite kernel scheme — is a finite flat morphism, here with abelian varieties presented as smooth proper $K$-schemes with connected fibres carrying a commutative group law on their functor of points. It is invoked in the construction of finite flat coverings arising from quaternionic correspondences, in [`CerednikDrinfeld.QM.surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt`](thm.html#CerednikDrinfeld.QM.surjective_and_isFinite_and_flat_of_mapPt_mapPt_eq_nsmulPt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
    {K : Type u} [Field K]
    {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} (LX : RelativeGroupLaw K fX)
    (hcX : LX.IsCommutative) (hX : AbelianSchemePropertyBundle K fX)
    {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of K)} (LY : RelativeGroupLaw K fY)
    (hcY : LY.IsCommutative) (hY : AbelianSchemePropertyBundle K fY)
    (u : SchemeHomOver fX fY)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fX),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) u =
        LY.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    (hsurj : Surjective u.1)
    (hker : IsFinite (pullback.snd u.1 (LY.one (𝟙 (Spec (CommRingCat.of K)))).1)) :
    IsFinite u.1 ∧ Flat u.1 := by sorry
