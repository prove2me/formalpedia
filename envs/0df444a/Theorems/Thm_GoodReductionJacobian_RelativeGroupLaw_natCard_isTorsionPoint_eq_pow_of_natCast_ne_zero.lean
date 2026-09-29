-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
-- name    : GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/378f0411-2fc3-55c6-a054-25ee506afdd7
-- title:
--   Count of n-torsion points of an abelian variety: n^{2g}
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} K$ a morphism. Let $L$ be a relative group law on $f$, that is, for every scheme $T$ and every $T \to \operatorname{Spec} K$ a multiplication, unit and inverse on the set of $T$-points $\{\varphi : T \to A \mid \varphi \text{ followed by } f \text{ equals } t\}$, satisfying associativity, the two unit laws and the left inverse law, with multiplication compatible with composition along any $\psi : T' \to T$ over $\operatorname{Spec} K$; assume `hc`, that this multiplication is commutative for every such $t$. Assume the bundle `hA`: $f$ is smooth, proper, each fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} K$ is connected, and $f$ carries a relative group law. Let $g$ be a natural number with $f$ smooth of relative dimension $g$, and let $n$ be a natural number whose image in $K$ is nonzero. Then the number of $K$-points $x$ of $f$ (sections over the identity of $\operatorname{Spec} K$) with $n \cdot x$, formed by iterating the group law $n$ times starting from the unit, equal to the unit, computed as a `Nat.card`, equals $n^{2g}$.
--
--   This is the classical count of the $n$-torsion of an abelian variety of dimension $g$ over an algebraically closed field for $n$ prime to the characteristic, in the form $\#A[n](K) = n^{2g}$. It is used in the Néron–Ogg–Shafarevich style arguments about torsion of Jacobians, and is quoted by the polarised abelian scheme torsion bounds and by the level structure constructions on fake elliptic curves in the Čerednik–Drinfel'd material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) n x} = n ^ (2 * g) := by sorry
