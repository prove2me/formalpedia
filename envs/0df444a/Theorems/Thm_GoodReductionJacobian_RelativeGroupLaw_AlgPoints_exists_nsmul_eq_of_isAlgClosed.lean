-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_AlgPoints_exists_nsmul_eq_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.AlgPoints.exists_nsmul_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/f048936e-fce1-5409-b5d8-43ea5477eb08
-- title:
--   n-divisibility of A(k) for k algebraically closed
-- statement:
--   Let $k$ be an algebraically closed field (a type in the lowest universe), let $A$ be a scheme and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes. Let $L$ be a relative group law for $f$ over $k$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ t = f\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} k$, with multiplication, unit and inverse satisfying associativity, the unit laws and left inversion, and with multiplication compatible with base change along any $\psi : T' \to T$ with $t \circ \psi = t'$ (written diagrammatically, $\psi \gg t = t'$). Assume $hc$: the law is commutative on every such set of points. Assume further the bundle $hA$ of properties of $f$: $f$ is smooth, $f$ is proper, each fibre $f^{-1}(s)$ is connected for every point $s$ of $\operatorname{Spec} k$, and $f$ admits at least one relative group law. Let $n$ be a natural number with $n \neq 0$ in $k$, and let $y$ be an element of $L.AlgPoints\ hc\ k$, i.e. the additive group obtained from the set of points over $\operatorname{Spec}$ of the structure map $k \to k$ with the group law $L$. Then there exists $y_1$ in that same group with $n \bullet y_1 = y$.
--
--   This is the classical statement that multiplication by $n$ is surjective on the group of $k$-points of an abelian variety over an algebraically closed field $k$ whose characteristic does not divide $n$, here phrased for the project's additive group of algebra points of a relative group law. It is used where a point must be divided by $n$, for instance when pulling theta-group commutators back along multiplication by $n$ in the identification of commutators with level pairings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_AlgPoints_exists_nsmul_eq_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.AlgPoints.exists_nsmul_eq_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (n : ℕ) (hn : (n : k) ≠ 0) (y : L.AlgPoints hc k) :
    ∃ y₁ : L.AlgPoints hc k, n • y₁ = y := by sorry
