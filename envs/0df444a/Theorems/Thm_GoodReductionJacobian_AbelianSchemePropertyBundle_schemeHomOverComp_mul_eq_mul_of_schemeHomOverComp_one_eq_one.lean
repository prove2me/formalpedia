-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/cd238fcb-47f0-5468-a020-fee99b829b64
-- title:
--   Unit-preserving morphism of abelian schemes is a homomorphism
-- statement:
--   Let $R$ be a commutative ring, and let $f : A \to \operatorname{Spec} R$ and $g : B \to \operatorname{Spec} R$ be morphisms of schemes (all in a fixed universe). Assume `AbelianSchemePropertyBundle R f` and `AbelianSchemePropertyBundle R g`, i.e. each of $f$ and $g$ is smooth and proper, each has connected fibres in the sense that the preimage under the underlying continuous map of every point of $\operatorname{Spec} R$ is a connected set, and each admits at least one relative group law. Let $L$ and $M$ be relative group laws for $f$ and for $g$ respectively: thus, functorially in an $R$-scheme $t : T \to \operatorname{Spec} R$, operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on the set $\{x : T \to A \mid x \text{ followed by } f = t\}$ of $T$-points over $t$, satisfying associativity, both unit laws, left inverses, and compatibility of $\mathrm{mul}$ with base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $\varphi : A \to B$ satisfy $\varphi$ followed by $g$ equals $f$, and suppose that composing the $L$-unit over the identity of $\operatorname{Spec} R$ with $\varphi$ gives the $M$-unit over the identity. Then for every scheme $T$, every $t : T \to \operatorname{Spec} R$ and all $T$-points $x, y$ of $A$ over $t$, composing $\mathrm{mul}_L(t,x,y)$ with $\varphi$ equals $\mathrm{mul}_M$ of the composites $x$ followed by $\varphi$ and $y$ followed by $\varphi$.
--
--   This is the rigidity consequence that a morphism of abelian schemes carrying the unit section to the unit section is a homomorphism on $T$-valued points, in the form of Corollary 6.4 of Geometric Invariant Theory. It is used in the development of the group structure on Jacobians with good reduction, in particular for the commutativity of a relative group law on an abelian scheme, for the uniqueness of a relative group law with given unit, and for the criterion that a morphism is multiplicative exactly when it respects units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one
    {R : Type u} [CommRing R] {A B : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (hB : AbelianSchemePropertyBundle R g)
    (L : RelativeGroupLaw R f) (M : RelativeGroupLaw R g) (φ : SchemeHomOver f g)
    (hφ : NeronModelInfra.schemeHomOverComp (L.one (𝟙 (Spec (CommRingCat.of R)))) φ = M.one (𝟙 (Spec (CommRingCat.of R)))) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) := by sorry
