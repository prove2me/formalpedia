-- Prove2me | Theorems.Thm_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero
-- name    : ModularCurve.two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/5cbd5fb9-ff77-51d7-9ec4-b5668a273824
-- title:
--   Points of X₀(N) with j-invariant 1728
-- statement:
--   Let $N$ be a natural number, nonzero, and let $L$ be an algebraically closed field in which $N$, $2$ and $3$ are all nonzero (so that the characteristic of $L$ divides none of $6N$; characteristic zero is allowed). Here `ModuliPoint N L` is the quotient of the type `Gamma0Pair N L` of pairs consisting of a Weierstrass curve over $L$ together with a proof that it is elliptic and a point `gen` of its affine points of additive order exactly $N$, by the relation `Gamma0Pair.Step`, which relates $P$ to $Q$ when there is a variable change $\gamma$ over $L$ carrying $P$'s curve to $Q$'s curve and a natural number $k$ coprime to $N$ with $Q$'s generator equal to $k$ times the image of $P$'s generator under `Point.vcInvFun` for $\gamma$; and `ModuliPoint.j` is the $j$-invariant attached to such a class. The assertion is that twice the cardinality of the subtype of classes $x$ in `ModuliPoint N L` with `ModuliPoint.j x` $= 1728$ equals $\psi(N) + \nu_2(N)$, where $\psi(N)$ is `dedekindPsi N` $= \sum_{d \mid N,\ d \text{ squarefree}} N/d$ and $\nu_2(N)$ is `nuTwo N`, the number of $x \in \mathbb{Z}/N\mathbb{Z}$ with $x^2 + 1 = 0$.
--
--   This is the count of the elliptic points of order $2$ on the modular curve $X_0(N)$, in the moduli-theoretic form $2\,\#\{(E,C) : j(E) = 1728\} = \psi(N) + \nu_2(N)$, valid over any algebraically closed field of characteristic not dividing $6N$; the factor $2$ records the action of $\operatorname{Aut}(E_{1728})/\{\pm 1\}$ on the $\psi(N)$ cyclic subgroups of order $N$. It feeds the ramification and genus computations for $X_0(N)$, being used in the counts of supersingular and elliptic places and in the fibre count for the $j$-map on the modular function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [DecidableEq L] [IsAlgClosed L]
    (hN : (N : L) ≠ 0) (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) :
    2 * Nat.card {x : ModuliPoint N L // ModuliPoint.j x = (1728 : L)} =
      dedekindPsi N + nuTwo N := by sorry
