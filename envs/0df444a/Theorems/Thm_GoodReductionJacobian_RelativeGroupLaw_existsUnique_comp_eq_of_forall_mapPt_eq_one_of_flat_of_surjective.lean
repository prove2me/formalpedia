-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective
-- name    : GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/9472221c-ad52-5b26-847a-f12645a8c028
-- title:
--   Descent of a homomorphism through a flat surjective quotient
-- statement:
--   Let $R$ be a commutative ring, let $D$, $E$, $X$ be schemes with structure morphisms $g_D : D \to \operatorname{Spec} R$, $g_E : E \to \operatorname{Spec} R$, $g_X : X \to \operatorname{Spec} R$, and let $L_D$, $L_E$, $L_X$ be relative group laws on them, i.e. for each $t : T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set of morphisms $T \to A$ over $t$ (pairs $\langle \varphi, \varphi \circ{} \text{(structure map)} = t\rangle$) satisfying associativity, the unit laws, left inverses, and compatibility with precomposition by morphisms $T' \to T$ over the base. Let $\psi : D \to E$ satisfy $g_E \circ \psi = g_D$ and be multiplicative on points, in the sense that for every $t : T \to \operatorname{Spec} R$ and all $T$-points $P, Q$ of $D$ over $t$ one has $\psi \circ (P \cdot_{L_D} Q) = (\psi \circ P) \cdot_{L_E} (\psi \circ Q)$; assume $\psi$ is flat, surjective and quasi-compact. Let $\chi : X \to{}$ — more precisely $\chi : D \to X$ with $g_X \circ \chi = g_D$ — be multiplicative in the same sense, and assume $\chi$ kills the kernel of $\psi$: whenever $\psi \circ P = L_E.\mathrm{one}(t)$ for a $T$-point $P$ of $D$ over $t$, then $\chi \circ P = L_X.\mathrm{one}(t)$. Then there exists $\bar\chi : E \to X$ with $g_X \circ \bar\chi = g_E$ such that $\bar\chi \circ \psi = \chi$, such that $\bar\chi$ is multiplicative on points for $L_E$ and $L_X$, and such that every morphism $E \to X$ over the base whose composite with $\psi$ is $\chi$ equals $\bar\chi$.
--
--   This is the functor-of-points form of the statement that a faithfully flat quasi-compact homomorphism of group schemes is the quotient by its kernel, so that any homomorphism trivial on that kernel descends uniquely. It is used in the construction of morphisms between quaternionic (fake elliptic curve) moduli objects, for instance to descend maps through isogenies and to compare quotients with extra level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_forall_mapPt_eq_one_of_flat_of_surjective
    (R : Type u) [CommRing R] {D E X : Scheme.{u}}
    {gD : D ⟶ Spec (CommRingCat.of R)} {gE : E ⟶ Spec (CommRingCat.of R)} {gX : X ⟶ Spec (CommRingCat.of R)}
    (LD : RelativeGroupLaw R gD) (LE : RelativeGroupLaw R gE) (LX : RelativeGroupLaw R gX)
    (ψ : D ⟶ E) (hψ : ψ ≫ gE = gD)
    (ψ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t gD),
      mapPt ψ hψ (LD.mul t P Q) = LE.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    [Flat ψ] [Surjective ψ] [QuasiCompact ψ]
    (χ : D ⟶ X) (hχ : χ ≫ gX = gD)
    (χ_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t gD),
      mapPt χ hχ (LD.mul t P Q) = LX.mul t (mapPt χ hχ P) (mapPt χ hχ Q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t gD),
      mapPt ψ hψ P = LE.one t → mapPt χ hχ P = LX.one t) :
    ∃ χ' : SchemeHomOver gE gX, ψ ≫ χ'.1 = χ ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (v w : SchemeHomOver t gE),
        mapPt χ'.1 χ'.2 (LE.mul t v w) = LX.mul t (mapPt χ'.1 χ'.2 v) (mapPt χ'.1 χ'.2 w)) ∧
      ∀ χ'' : SchemeHomOver gE gX, ψ ≫ χ''.1 = χ → χ'' = χ' := by sorry
