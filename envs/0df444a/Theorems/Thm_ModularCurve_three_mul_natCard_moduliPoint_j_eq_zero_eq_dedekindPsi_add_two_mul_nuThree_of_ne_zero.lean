-- Prove2me | Theorems.Thm_ModularCurve_three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree_of_ne_zero
-- name    : ModularCurve.three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/52783608-4f57-514b-b1d3-c76339c5b9b3
-- title:
--   Count of moduli points with j=0: ψ(N)+2ν₃(N)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, and let $L$ be an algebraically closed field in which $N$, $2$ and $3$ are all nonzero (equivalently, $\operatorname{char} L$ divides neither $6$ nor $N$; characteristic $0$ is allowed). Here `ModuliPoint N L` is the quotient of the type `Gamma0Pair N L` of triples consisting of a Weierstrass curve $W$ over $L$ that is elliptic together with a point `gen` of its affine model of additive order exactly $N$, by the relation that sends $P$ to $Q$ when there is a Weierstrass variable change $\gamma$ with $\gamma \cdot P.\mathrm{toCurve} = Q.\mathrm{toCurve}$ and a natural number $k$ coprime to $N$ such that $Q.\mathrm{gen}$ is $k$ times the image of $P.\mathrm{gen}$ under the transport of points along $\gamma$; `ModuliPoint.j` is the induced $j$-invariant. The assertion is the equality of natural numbers
--   $$3 \cdot \#\{x \in \mathrm{ModuliPoint}\ N\ L : j(x) = 0\} = \psi(N) + 2\,\nu_3(N),$$
--   where $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$ (the Dedekind psi function, $N\prod_{p \mid N}(1 + 1/p)$) and $\nu_3(N)$ is the number of $x \in \mathbb{Z}/N\mathbb{Z}$ with $x^2 + x + 1 = 0$.
--
--   This is the count of the elliptic points of order $3$ on the coarse moduli space $Y_0(N)$, in the form used for the genus formula: the fibre of the $j$-map over $j = 0$ has $(\psi(N) + 2\nu_3(N))/3$ elements, so $\nu_3(N)$ of the $\psi(N)$ cyclic $N$-subgroups of a curve with $j = 0$ give points with nontrivial automorphisms. It feeds the computations of the numerical invariants of $X_0(N)$ and of supersingular point counts, being cited by [`ModularCurve.card_eq_nuTwo_and_card_eq_nuThree_of_forall_mem_iff_placeWidth_eq`](thm.html#ModularCurve.card_eq_nuTwo_and_card_eq_nuThree_of_forall_mem_iff_placeWidth_eq), [`ModularCurve.card_eq_ssCountFormula_of_ssPlaces`](thm.html#ModularCurve.card_eq_ssCountFormula_of_ssPlaces) and [`ModularCurve.card_fibres_jqModC_modularFunctionFieldFullC_eq`](thm.html#ModularCurve.card_fibres_jqModC_modularFunctionFieldFullC_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree_of_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree_of_ne_zero
    (N : ℕ) [NeZero N] (L : Type*) [Field L] [DecidableEq L] [IsAlgClosed L]
    (hN : (N : L) ≠ 0) (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) :
    3 * Nat.card {x : ModuliPoint N L // ModuliPoint.j x = (0 : L)} =
      dedekindPsi N + 2 * nuThree N := by sorry
