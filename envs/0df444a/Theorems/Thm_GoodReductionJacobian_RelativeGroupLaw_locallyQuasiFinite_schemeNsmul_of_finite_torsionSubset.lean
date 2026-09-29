-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset
-- name    : GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/9f4626cb-8d8f-593d-9246-9816dedb3b7f
-- title:
--   Locally quasi-finite [n] from finite geometric n-torsion
-- statement:
--   Let $k$ be a field, let $G$ be a scheme and let $f \colon G \to \operatorname{Spec} k$ be a morphism that is locally of finite type. Let $L$ be a relative group law on $f$ in the sense of the project: for every scheme $T$ and every structure morphism $t \colon T \to \operatorname{Spec} k$, a multiplication, unit and inversion on the set $\{\varphi \colon T \to G \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $G$ over $t$, satisfying associativity, the two unit laws and left inverse, and compatible with precomposition by morphisms $\psi \colon T' \to T$ over $\operatorname{Spec} k$. Assume $L$ is commutative, i.e. $L.\mathrm{mul}\ t\ x\ y = L.\mathrm{mul}\ t\ y\ x$ for all $t$ and all points $x,y$ over $t$. Let $K$ be an algebraically closed field with a $k$-algebra structure, and let $n$ be a natural number. Assume the set of points $x$ of $G$ over the structure morphism $\operatorname{Spec} K \to \operatorname{Spec} k$ with $L$-iterate $n \cdot x$ (defined by recursion: $0 \cdot x$ is the unit and $(m+1) \cdot x = L.\mathrm{mul}(m\cdot x, x)$) equal to the unit point is finite. Then the morphism $L.\mathtt{schemeNsmul}\ n \colon G \to G$, namely the underlying morphism of the $n$-fold $L$-iterate of the identity point $\mathrm{id}_G$ viewed as a point of $G$ over $f$ itself, is locally quasi-finite.
--
--   This is the statement that multiplication by $n$ on a commutative group scheme locally of finite type over a field is locally quasi-finite as soon as the geometric $n$-torsion is finite; the group scheme is presented through its functor of points, so $[n]$ is the $n$-fold sum of the identity point. It is used in the study of $n$-divisibility on Jacobians and Picard schemes, and in the verification that multiplication by $n$ on fibres of models of modular curves is locally quasi-finite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset
    {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (n : ℕ)
    (hfin : (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap k K))) n).Finite) :
    LocallyQuasiFinite (L.schemeNsmul n) := by sorry
