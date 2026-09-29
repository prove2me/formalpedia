-- Prove2me | Theorems.Thm_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo
-- name    : ModularCurve.two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/9d84969f-c088-5295-91e3-6d4fc3146888
-- title:
--   Moduli points with j=1728: 2 #=ψ(N)+ν₂(N)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $L$ be an algebraically closed field equipped with a $\mathbb{Q}$-algebra structure (so of characteristic zero). The set `ModuliPoint N L` is the quotient, in the sense of `Quot`, of the type of pairs consisting of a Weierstrass curve over $L$ that is elliptic together with a point `gen` of its affine model whose additive order is exactly $N$, by the relation `Gamma0Pair.Step`, which relates $P$ to $Q$ when there is a Weierstrass variable change $\gamma$ over $L$ carrying the curve of $P$ to the curve of $Q$ and a natural number $k$ coprime to $N$ with the marked point of $Q$ equal to $k$ times the image of the marked point of $P$ under `Point.vcInvFun` for $\gamma$; thus classes correspond to pairs (elliptic curve, cyclic subgroup of order $N$) up to isomorphism. The assertion is that twice the cardinality of the subtype of those classes $x$ with `ModuliPoint.j x` equal to $1728$, the $j$-invariant of the underlying curve, equals $\mathrm{dedekindPsi}(N) + \nu_2(N)$, where $\mathrm{dedekindPsi}(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d = N\prod_{p \mid N}(1 + 1/p)$ and $\nu_2(N)$ is the number of $x \in \mathbb{Z}/N$ with $x^2 + 1 = 0$.
--
--   This is the moduli-theoretic form of the count of points of $Y_0(N)$ above $j = 1728$: the fibre has $(\psi(N) + \nu_2(N))/2$ elements, the extra order-$2$ automorphism of a curve with $j = 1728$ pairing up the $\psi(N)$ cyclic subgroups of order $N$ except at the $\nu_2(N)$ fixed ones, which are the elliptic points of order $2$ of $\Gamma_0(N)$. It feeds the computations of ramification of $X_0(N) \to X(1)$ above $j = 1728$ and $j = 0$ used by [`ModularCurve.card_filter_ord_jBar_sub_1728_eq_one_eq_nuTwo`](thm.html#ModularCurve.card_filter_ord_jBar_sub_1728_eq_one_eq_nuTwo), [`ModularCurve.natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo`](thm.html#ModularCurve.natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo) and [`ModularCurve.natCard_ord_jBar_eq_one_eq_nuThree`](thm.html#ModularCurve.natCard_ord_jBar_eq_one_eq_nuThree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo.lean

import Mathlib
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [DecidableEq L] [Algebra ℚ L] [IsAlgClosed L] :
    2 * Nat.card {x : ModuliPoint N L // ModuliPoint.j x = (1728 : L)} = dedekindPsi N + nuTwo N := by sorry
