-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_faithfullyFlat_mul_self_eq_schemeHomOverComp
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_faithfullyFlat_mul_self_eq_schemeHomOverComp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/9cd97a10-24f2-5dbc-b82e-16ebcd53d1a9
-- title:
--   Halving a point after a faithfully flat base extension
-- statement:
--   Let $k$ be a field and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes (in universe $0$) equipped with a relative group law $L$, that is, a functorial group structure on the sets $\operatorname{SchemeHomOver}(t, f) = \{\varphi : T \to A \mid \varphi \circ t^{-1}\text{-compatible}\}$, more precisely the set of morphisms $\varphi : T \to A$ with $f \circ \varphi = t$, for each $t : T \to \operatorname{Spec} k$, with multiplication, unit and inverse satisfying associativity, unit and inverse laws and compatible with base change along any $\psi : T' \to T$ over $\operatorname{Spec} k$. Assume $L$ is commutative, i.e. $L.\mathrm{mul}\,t\,x\,y = L.\mathrm{mul}\,t\,y\,x$ for all $t$ and all $x, y$, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, $f$ is proper, every fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} k$ is connected, and a relative group law on $f$ exists. Let $R$ be a commutative ring, let $t : \operatorname{Spec} R \to \operatorname{Spec} k$, and let $x$ be a point of $A$ over $t$, i.e. a morphism $\operatorname{Spec} R \to A$ whose composite with $f$ is $t$. Then there exist a commutative ring $R'$ and an $R$-algebra structure on $R'$ such that $R'$ is faithfully flat as an $R$-module, together with a point $y$ of $A$ over the composite $\operatorname{Spec} R' \to \operatorname{Spec} R \to \operatorname{Spec} k$, satisfying $L.\mathrm{mul}\,y\,y = x|_{R'}$, where $x|_{R'}$ denotes the base change of $x$ along $\operatorname{Spec}$ of the structure map $R \to R'$.
--
--   This is the statement that multiplication by $2$ on an abelian scheme over a field is an epimorphism for the faithfully flat topology: every point with values in a ring $R$ becomes divisible by $2$ after a faithfully flat extension of $R$. It is used in the study of polarisations, namely by [`AlgebraicGeometry.Polarisation.kernelTrivial_of_nonempty_iso_tensor_self_of_kernelIsTwoTorsion`](thm.html#AlgebraicGeometry.Polarisation.kernelTrivial_of_nonempty_iso_tensor_self_of_kernelIsTwoTorsion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_faithfullyFlat_mul_self_eq_schemeHomOverComp.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry GoodReductionJacobian AlgebraicGeometry.Polarisation
open NeronModelInfra

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_faithfullyFlat_mul_self_eq_schemeHomOverComp
    (k : Type) [Field k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R'),
      Module.FaithfullyFlat R R' ∧
      ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ t) f,
        L.mul _ y y = GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (algebraMap R R'))) rfl x := by sorry
