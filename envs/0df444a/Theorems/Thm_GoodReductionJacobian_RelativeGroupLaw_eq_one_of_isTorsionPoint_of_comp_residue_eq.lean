-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_isTorsionPoint_of_comp_residue_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.eq_one_of_isTorsionPoint_of_comp_residue_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/74db318a-85fa-5146-b8c8-6c42605d2a32
-- title:
--   Torsion of invertible order injects into the residue fibre
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $f : X \to \operatorname{Spec} R$ a morphism which is locally of finite type, and let $L$ be a relative group law on $f$ over $R$: for every test scheme $T$ and every $t : T \to \operatorname{Spec} R$ it provides a multiplication, a unit and an inversion on the set of $T$-points over $t$, that is, on morphisms $\varphi : T \to X$ with $\varphi$ followed by $f$ equal to $t$, satisfying associativity, both unit laws and left inversion, with multiplication natural under precomposition by a morphism $\psi : T' \to T$ over $\operatorname{Spec} R$; assume moreover that $L$ is commutative, i.e. the multiplication on points over any $t$ is commutative. Let $B$ be a commutative local ring, $t : \operatorname{Spec} B \to \operatorname{Spec} R$ a morphism, and $m$ a natural number whose image in $B$ is a unit. Let $s$ be a point of $X$ over $t$, and suppose that $s$ is $m$-torsion, in the sense that the $m$-fold iterate $\operatorname{nsmul}$ of the multiplication applied to $s$ (defined by $0 \cdot s = L.\mathrm{one}$, $(n+1)\cdot s = (n\cdot s)\, s$) equals $L.\mathrm{one}\, t$, and that $s$ and $L.\mathrm{one}\, t$ become equal after precomposition with $\operatorname{Spec}$ of the residue map $B \to B/\mathfrak m_B$. Then $s = L.\mathrm{one}\, t$.
--
--   This is the rigidity statement of Serre and Tate for the kernel of reduction: a $B$-point of order $m$ with $m$ invertible in the local ring $B$ which reduces to the identity on the residue field is the identity, so that $m$-torsion injects into the residue fibre. No smoothness or separatedness of $f$ is assumed, only local finiteness of type and a commutative relative group law. It is used to pin down the toric and finite parts of Néron objects attached to modular curves by conditions on reduction, and in the study of fake elliptic curves over valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_isTorsionPoint_of_comp_residue_eq.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry GoodReductionJacobian
open NeronModelInfra hiding schemeHomOverComp

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.eq_one_of_isTorsionPoint_of_comp_residue_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) [LocallyOfFiniteType f]
    {B : Type u} [CommRing B] [IsLocalRing B]
    (t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (m : ℕ) (hm : IsUnit (m : B))
    (s : SchemeHomOver t f)
    (hs : L.IsTorsionPoint t m s)
    (hred : schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) rfl s =
        schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) rfl (L.one t)) :
    s = L.one t := by sorry
