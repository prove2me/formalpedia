-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_pullback_schemeKerStr_residueField_of_isUnit
-- name    : GoodReductionJacobian.RelativeGroupLaw.isReduced_pullback_schemeKerStr_residueField_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/1d752036-89bb-57a7-ac2a-abfc5a2dc00f
-- title:
--   Reduced special fibre of the n-torsion kernel for n invertible
-- statement:
--   Let $R$ be a commutative local ring and let $f\colon A\to\operatorname{Spec} R$ be a morphism of schemes that is locally of finite type. Let $G$ be a relative group law on $f$ over $R$: for every scheme $T$ and every morphism $t\colon T\to\operatorname{Spec} R$ it provides a multiplication, a unit and an inverse on the set of $T$-points of $A$ over $t$, i.e. on morphisms $\varphi\colon T\to A$ with $\varphi$ followed by $f$ equal to $t$, satisfying associativity, the unit laws and left inversion, and with multiplication compatible with precomposition by any $\psi\colon T'\to T$ over $\operatorname{Spec} R$. Assume furthermore that all these multiplications are commutative, and let $n$ be a natural number whose image in $R$ is a unit. Write `G.schemeNsmul n` for the endomorphism of $A$ underlying the $n$-fold multiple of the identity point of $A$ over $f$, and let `G.schemeKerStr n` be the second projection from the fibre product of `G.schemeNsmul n` with the unit section $\operatorname{Spec} R\to A$ down to $\operatorname{Spec} R$. The conclusion is that the pullback of `G.schemeKerStr n` along $\operatorname{Spec}$ of the residue map $R\to \kappa$, $\kappa$ the residue field of $R$, is a reduced scheme.
--
--   This is the statement that the special fibre of the kernel of multiplication by $n$ is reduced (indeed étale) when $n$ is invertible on the base, the classical fact that an unramified finite-type scheme over a field is reduced applied to torsion subschemes of a relative group. It is used downstream in the analysis of the $n$-torsion of Néron models of Jacobians of modular curves at a prime, where the reducedness of the special fibre enters the comparison of the rank of the torsion with the cardinality of the group of torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_pullback_schemeKerStr_residueField_of_isUnit.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isReduced_pullback_schemeKerStr_residueField_of_isUnit
    {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    IsReduced (pullback (G.schemeKerStr n)
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))) := by sorry
