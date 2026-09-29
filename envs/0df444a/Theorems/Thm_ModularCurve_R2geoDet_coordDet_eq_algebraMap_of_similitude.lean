-- Prove2me | Theorems.Thm_ModularCurve_R2geoDet_coordDet_eq_algebraMap_of_similitude
-- name    : ModularCurve.R2geoDet.coordDet_eq_algebraMap_of_similitude
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/0f26cfc5-c2e8-5642-a112-dcc5f7f59577
-- title:
--   Coordinate determinant of a similitude equals its factor
-- statement:
--   Let $K$ be a field of characteristic zero, $A$ a commutative $K$-algebra, and $V$ an additive group carrying compatible $K$- and $A$-module structures (a scalar tower $K \to A \to V$). Assume given: an $A$-basis $b$ of $V$ indexed by `Fin 2`; a $K$-bilinear form $B : V \to V \to K$ which is balanced for the $A$-action, $B(a \cdot v, w) = B(v, a \cdot w)$ for all $a \in A$ and $v, w \in V$, alternating in the strong sense $B(v,v) = 0$ for all $v$, and nondegenerate in the left slot in the sense that $B(v,w) = 0$ for all $w$ forces $v = 0$; a $K$-linear endomorphism $f$ of $V$ that is $A$-equivariant, $f(a \cdot v) = a \cdot f(v)$; and a scalar $c \in K$ such that $B(f v, f w) = c \cdot B(v,w)$ for all $v,w$. The conclusion is an identity in $A$ between the $2 \times 2$ determinant of the coordinate matrix of $f$ in the basis $b$ and the image of the similitude factor: with $(b.repr\,x)_i \in A$ denoting the $i$-th coordinate of $x$, $$(b.repr(f(b_0)))_0 (b.repr(f(b_1)))_1 - (b.repr(f(b_1)))_0 (b.repr(f(b_0)))_1 = \mathrm{algebraMap}_{K \to A}(c).$$
--
--   This is the determinant identity for a similitude of a balanced alternating pairing on a module of rank two, stated at the level of coordinates in a chosen $A$-basis rather than via `LinearMap.det`, and with no finiteness or faithfulness assumptions. It is used to compute the determinant of a Frobenius element acting on a rank-two module of Tate-module type from the similitude property of the associated pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_R2geoDet_coordDet_eq_algebraMap_of_similitude.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.R2geoDet.coordDet_eq_algebraMap_of_similitude
    {K : Type} [Field K] [CharZero K]
    {A : Type} [CommRing A] [Algebra K A]
    {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
    (b : Module.Basis (Fin 2) A V)
    (B : V →ₗ[K] V →ₗ[K] K)
    (hbal : ∀ (a : A) (v w : V), B (a • v) w = B v (a • w))
    (halt : ∀ v : V, B v v = 0)
    (hnd : ∀ v : V, (∀ w : V, B v w = 0) → v = 0)
    (f : V →ₗ[K] V) (hfA : ∀ (a : A) (v : V), f (a • v) = a • f v)
    (c : K) (hsim : ∀ v w : V, B (f v) (f w) = c • B v w) :
    (b.repr (f (b 0))) 0 * (b.repr (f (b 1))) 1
      - (b.repr (f (b 1))) 0 * (b.repr (f (b 0))) 1
    = algebraMap K A c := by sorry
