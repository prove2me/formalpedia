-- Prove2me | Theorems.Thm_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1
-- name    : ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/6afd7dca-6a3d-5d97-874a-22a33c55b1d3
-- title:
--   Orders of j and j-1728 on X₁(M) for M≥ 4
-- statement:
--   Let $K$ be an algebraically closed field equipped with a $\mathbb{Q}$-algebra structure (so of characteristic $0$), and let $M$ be a nonzero natural number with $4 \le M$. Let $F_0 =$ `qExpFunctionFieldC ℚ (Gamma1 M)` be the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by all quotients $P_f/P_g$ of $q$-expansions, where $f$ and $g$ are modular forms of one and the same weight $k$ for $\Gamma_1(M)$ (regarded inside $\mathrm{GL}_2(\mathbb{R})$) whose $q$-expansions are given by integral power series $P_f, P_g$ with $P_g \ne 0$ in $\mathbb{Q}((q))$; and let $F =$ `laurentBaseChange K F₀` be the subfield of $K((q))$ generated over $K$ by the image of $F_0$ under coefficientwise application of $\mathbb{Q} \to K$. Let $y \in F$ be an element whose underlying Laurent series is `jqModC K`, namely $q^{-1}$ times the image in $K[[q]]$ of the integral power series $E_4^3 \cdot \Delta^{-1}$, i.e. the $q$-expansion of the modular invariant $j$. The assertion is the conjunction of two statements about all places $P$ of $F$ over $K$, a place being a valuation subring of $F$ containing $K$, distinct from $F$ itself and a principal ideal ring, with $P.\mathrm{ord}$ the associated normalised integer valuation: first, for every such $P$, if $\mathrm{ord}_P(y) > 0$ then $\mathrm{ord}_P(y) = 3$; second, for every such $P$, if $\mathrm{ord}_P(y - 1728) > 0$ then $\mathrm{ord}_P(y - 1728) = 2$.
--
--   This is the statement that $X_1(M)$ has no elliptic points for $M \ge 4$, in the form that every zero of $j$ on the curve has order exactly $3$ and every zero of $j-1728$ order exactly $2$: the covering $X_1(M) \to X(1)$ is unramified over $j = 0$ and $j = 1728$. It is used to compute ramification indices for $X_1(M) \to X(1)$, parities of orders of modular forms at places, and thereby the genus of $X_1(M)$; the case $K = \overline{\mathbb{Q}}$ is transferred to general algebraically closed $K$ of characteristic $0$ by comparison of places under coefficientwise base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (M : ℕ) [NeZero M] (hM : 4 ≤ M)
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :
    (∀ P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))), 0 < P.ord y → P.ord y = 3) ∧
      (∀ P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))), 0 < P.ord (y - 1728) → P.ord (y - 1728) = 2) := by sorry
