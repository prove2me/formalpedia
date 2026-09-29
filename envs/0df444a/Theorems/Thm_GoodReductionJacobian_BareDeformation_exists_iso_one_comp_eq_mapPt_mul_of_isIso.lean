-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso
-- name    : GoodReductionJacobian.BareDeformation.exists_iso_one_comp_eq_mapPt_mul_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/1f4a5c74-0176-53c9-b64d-24eef3ba7551
-- title:
--   Isomorphic bare deformations admit a unit-preserving, multiplicative isomorphism
-- statement:
--   Let $B$ and $B_1$ be commutative rings with $B_1$ a $B$-algebra, let $A_1$ be a scheme, $f_1 : A_1 \to \operatorname{Spec} B_1$ a morphism and $L_1$ a relative group law for $f_1$, that is, a functorial commutative-free group structure on the sets $\{\varphi : T \to A_1 \mid \varphi \circ f_1 = t\}$ of sections over varying $t : T \to \operatorname{Spec} B_1$, natural in $T$. Let $D, D'$ be bare deformations of $(f_1, L_1)$ to $B$: each consists of a scheme $A$, a morphism $f : A \to \operatorname{Spec} B$, a commutative relative group law $L$ on $f$, the assertion that $f$ is smooth, proper, with connected fibres and carries a relative group law, a morphism $g : A_1 \to A$ making the square with $f_1$, $f$ and $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ cartesian, and the requirement that $g$ carries $L_1$-multiplication of sections to $L$-multiplication. Assume `D.IsIso D'`: there is an isomorphism $D.A \cong D'.A$ commuting with the structure morphisms to $\operatorname{Spec} B$ and with the maps from $A_1$. Then there are an isomorphism $e : D.A \cong D'.A$ and a proof $he$ that $e$ followed by $D'.f$ equals $D.f$ such that $D.g$ followed by $e$ equals $D'.g$, the unit section of $D.L$ over the identity of $\operatorname{Spec} B$ followed by $e$ is the unit section of $D'.L$, and for every scheme $T$, every $t : T \to \operatorname{Spec} B$ and all sections $P, Q$ of $D.f$ over $t$, composing with $e$ (via `mapPt`) takes $D.L.mul\ t\ P\ Q$ to $D'.L.mul$ of the images of $P$ and $Q$.
--
--   This upgrades an arbitrary isomorphism of bare deformations to one that preserves the zero section and is a homomorphism of the relative group laws, the rigidity phenomenon for pointed morphisms of abelian schemes; the group-law compatibility is supplied by the cited rigidity lemma for property bundles. It is used in the analysis of shifts and regluings of bare deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_iso_one_comp_eq_mapPt_mul_of_isIso.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped TensorProduct

theorem GoodReductionJacobian.BareDeformation.exists_iso_one_comp_eq_mapPt_mul_of_isIso
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D D' : BareDeformation f₁ L₁ B) (h : D.IsIso D') :
    ∃ (e : D.A ≅ D'.A) (he : e.hom ≫ D'.f = D.f), D.g ≫ e.hom = D'.g ∧
      (D.L.one (𝟙 _)).1 ≫ e.hom = (D'.L.one (𝟙 _)).1 ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
        mapPt e.hom he (D.L.mul t P Q) = D'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q) := by sorry
