-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_mapPt_schemeNsmul_mul
-- name    : GoodReductionJacobian.RelativeGroupLaw.mapPt_schemeNsmul_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/112e4715-6db2-5ab0-8434-4d1cbf5bdf10
-- title:
--   Multiplication by m is a homomorphism on T-points
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a structure morphism, and let $L$ be a relative group law on $f$: that is, a functorial assignment, to each scheme $T$ with a morphism $t : T \to \operatorname{Spec} R$, of a multiplication, unit and inversion on the set $\mathrm{SchemeHomOver}\ t\ f$ of morphisms $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, satisfying associativity, the unit laws, left inverses, and compatibility with base change along any $\psi : T' \to T$ over $\operatorname{Spec} R$. Assume $L$ is commutative, i.e. $L.\mathrm{mul}\ t\ x\ y = L.\mathrm{mul}\ t\ y\ x$ for all $t$ and all points $x, y$ over $t$. Fix $m \in \mathbb{N}$ and let $[m] = L.\mathrm{schemeNsmul}\ m : A \to A$ be the underlying morphism of the $m$-fold $L$-product of the identity point $\mathrm{id}_A$ with itself, together with the identity $[m]$ followed by $f$ equals $f$. Then for every $t : T \to \operatorname{Spec} R$ and all points $P, Q$ over $t$, post-composing with $[m]$ is multiplicative: $(L.\mathrm{mul}\ t\ P\ Q)$ followed by $[m]$ equals $L.\mathrm{mul}\ t$ applied to $P$ followed by $[m]$ and $Q$ followed by $[m]$.
--
--   This is the statement that the multiplication-by-$m$ endomorphism of a commutative relative group scheme is a group homomorphism, expressed at the level of $T$-points and of post-composition with the morphism $[m]$. It supplies the homomorphism hypothesis used when theta-group commutators are pulled back along $[m]$ in the comparison of commutators with level-pairing values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_mapPt_schemeNsmul_mul.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.mapPt_schemeNsmul_mul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (m : ℕ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) (L.mul t P Q) =
      L.mul t (CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) P)
        (CerednikDrinfeld.QM.mapPt (L.schemeNsmul m) (L.schemeNsmul_over m) Q) := by sorry
