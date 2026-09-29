-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_opens_forall_mul_base_mem_of_forall_specializes_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/e547a8e9-82a1-5ce8-9319-78c4012b351b
-- title:
--   Open locus of good translators over a discrete valuation ring
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain), let $B$ be a scheme and let $g\colon B \to \operatorname{Spec} R$ be smooth, separated and quasi-compact. Let $LB$ be a relative group law for $g$, that is, a group structure on each set $\{\varphi\colon T \to B \mid \varphi \circ g = t\}$ of $B$-points over a base morphism $t\colon T \to \operatorname{Spec} R$, associative with two-sided unit and left inverses, and compatible with composition $\psi$ along changes of base $T' \to T$. Let $U$ be an open subset of $B$ containing every point $b$ which admits no generization other than itself inside its own $g$-fibre (every $y$ with $y \rightsquigarrow b$ and $g(y) = g(b)$ equals $b$), and let $S$ be a finite set of points of $B$. Then there is an open $Z \subseteq B$ which contains some point lying over the closed point of $R$, and such that for every $z \in Z$ lying over the closed point of $R$, every local ring $R'$ that is an $R$-algebra, finite as an $R$-module, whose structure map is a local homomorphism, every $R$-morphism $\gamma\colon \operatorname{Spec} R' \to B$ carrying the closed point of $R'$ to $z$, every field $K$ and every pair $x\colon \operatorname{Spec} K \to B$, $t\colon \operatorname{Spec} K \to \operatorname{Spec} R'$ with $x$ and $t$ inducing the same morphism to $\operatorname{Spec} R$: if $x$ sends the closed point of $\operatorname{Spec} K$ into $S$, then the $LB$-product, over the base morphism $\operatorname{Spec} K \to \operatorname{Spec} R$, of $\gamma \circ t$ with $x$ sends the closed point of $\operatorname{Spec} K$ into $U$.
--
--   This is the point-set core of the standard translation argument for smooth separated group schemes over a discrete valuation ring: it produces an open set of potential translators $\gamma$, meeting the special fibre, all of whose integral points move a prescribed finite set of points into a given fibrewise large open $U$. It is used by [`GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing), where $\gamma$ is obtained from a section over a finite local extension of a henselian base, to place finitely many points in a common affine open.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_forall_mul_base_mem_of_forall_specializes_mem
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (S : Finset B) :
    ∃ Z : B.Opens, (∃ z : B, z ∈ Z ∧ g.base z = IsLocalRing.closedPoint R) ∧
      ∀ z : B, z ∈ Z → g.base z = IsLocalRing.closedPoint R →
      ∀ (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
        [Module.Finite R R']
        (γ : Spec (CommRingCat.of R') ⟶ B) (hγ : γ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        γ.base (IsLocalRing.closedPoint R') = z →
      ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B)
        (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
        (hx : x ≫ g = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        x.base (IsLocalRing.closedPoint K) ∈ S →
        (LB.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
            (schemeHomOverComp t rfl (⟨γ, hγ⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g))
            ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U := by sorry
