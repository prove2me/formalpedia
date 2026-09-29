-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_schemeKer_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/ccc31ca0-a3b8-57f7-9cf0-4d225da86464
-- title:
--   Kernel of [n] as a commutative group object
-- statement:
--   Let $R$ be a commutative ring, $J$ a scheme and $f \colon J \to \operatorname{Spec} R$, and let $L$ be a relative group law on $f$: that is, for every test morphism $t \colon T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set $\{\varphi \colon T \to J \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $f$, satisfying associativity, both unit laws, the left inverse law, and naturality of the multiplication under base change along any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume in addition that the multiplication is commutative for every $t$, and let $n$ be a natural number. Write $J[n]$ for the pullback of the scheme-level morphism $L.\mathrm{schemeNsmul}\,n \colon J \to J$ (the underlying morphism of the $n$-fold power of the identity point) along the unit section $\operatorname{Spec} R \to J$, with structure morphism $L.\mathrm{schemeKerStr}\,n$ the second pullback projection. The assertion is that there exist a group-object structure on $\mathrm{Over.mk}(L.\mathrm{schemeKerStr}\,n)$ in the category of schemes over $\operatorname{Spec} R$, together with the property that this monoid object is commutative, and a family of bijections $\mathrm{pts}$, one for each $t \colon T \to \operatorname{Spec} R$, from $\operatorname{Hom}_{/\operatorname{Spec} R}(T, J[n])$ onto the $n$-torsion subset of $T$-points of $f$ (those $x$ whose $n$-th power for $L$ equals $L.\mathrm{one}\,t$), such that $\mathrm{pts}$ carries the group-object product $a \cdot b$ of two such morphisms to $L.\mathrm{mul}\,t$ of their images, and is natural: for $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, the image of the composite of $\psi$ (as a morphism over $\operatorname{Spec} R$) with $a$ is $\psi$ followed by the image of $a$.
--
--   This is the statement that the $[n]$-kernel of a commutative relative group law on $J \to \operatorname{Spec} R$ is a commutative group scheme over $\operatorname{Spec} R$ whose functor of points is the $n$-torsion subfunctor, the group structure and the identification of points being produced simultaneously. It feeds the constructions of the Hopf-algebra structure on the $n$-torsion in the finite flat case, [`GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat) and [`GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat_schemeNsmul`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat_schemeNsmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory NeronModelInfra
  GoodReductionJacobian
open scoped CategoryTheory.MonObj

universe u
set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_schemeKer_eq
    {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) :
    ∃ (_ : GrpObj (Over.mk (L.schemeKerStr n))) (_ : IsCommMonObj (Over.mk (L.schemeKerStr n))),
      ∃ pts : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
          (Over.mk t ⟶ Over.mk (L.schemeKerStr n)) ≃ L.torsionSubset t n,
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
            (a b : Over.mk t ⟶ Over.mk (L.schemeKerStr n)),
          (↑(pts t (a * b)) : SchemeHomOver t f) =
            L.mul t (↑(pts t a)) (↑(pts t b))) ∧
        (∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
            (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
            (a : Over.mk t ⟶ Over.mk (L.schemeKerStr n)),
          (↑(pts t' (Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ a)) : SchemeHomOver t' f) =
            schemeHomOverComp ψ hψ (↑(pts t a))) := by sorry
