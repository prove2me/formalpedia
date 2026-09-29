-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback_of_isAlgClosed
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/e542522f-74e7-507d-9eac-714c45b87823
-- title:
--   Global functions on a geometric fibre of an abelian scheme
-- statement:
--   Let $T$ be a commutative ring and $f_0 \colon A_0 \to \operatorname{Spec} T$ a morphism of schemes satisfying the predicate `AbelianSchemePropertyBundle`, i.e. $f_0$ is smooth, $f_0$ is proper, for every point $s$ of $\operatorname{Spec} T$ the set-theoretic fibre $f_0^{-1}(\{s\})$ of the underlying continuous map is connected (non-empty and preconnected), and the type of relative group laws on $f_0$ is non-empty, a relative group law being a functorial group structure on the sets of $T$-morphisms $t \to f_0$ from arbitrary $T$-schemes, with multiplication, unit and inverse satisfying associativity, the unit laws and left inversion, and with multiplication compatible with composition in the source. Let $k$ be an algebraically closed field, $\rho \colon T \to k$ a ring homomorphism, and let $f_k \colon A_k \to \operatorname{Spec} k$ together with $i_0 \colon A_k \to A_0$ form a cartesian square over $\operatorname{Spec}\rho$, so that $A_k$ is presented as the geometric fibre of $f_0$ along $\rho$. Then the ring homomorphism $k \to \Gamma(A_k, \mathcal O_{A_k})$ obtained from the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} k, \mathcal O) \cong k$ followed by the map $f_k^{\sharp}$ on global sections is bijective on underlying sets.
--
--   This is the statement $\Gamma(A_k,\mathcal O_{A_k}) = k$ for the geometric fibre of an abelian scheme, the standard normalisation input for rigidity and for Künneth-type computations of $H^0$. It is used in the construction of lifts of the group law, in [`GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_mul_lift_of_isPullback_of_ker_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback_of_isAlgClosed
    {T : Type u} [CommRing T] {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of T)}
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {k : Type u} [Field k] [IsAlgClosed k] (ρ : T →+* k)
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of k)) (i₀ : Ak ⟶ A₀)
    (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ))) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fk.appTop).hom := by sorry
