-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree
-- name    : ModularCurve.exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/1e5108ef-a335-5cb0-b8cf-e6d13f1adb08
-- title:
--   Riemann–Roch spaces strictly grow at each place in large degree
-- statement:
--   Let $N$ be a nonzero natural number and write $K = \overline{\mathbb{Q}}$ (an algebraic closure of $\mathbb{Q}$) and $F =$ `modularFunctionFieldBar N`, the intermediate field of the Laurent series field $K((t))$ obtained by adjoining to $K$ the image, under the coefficientwise embedding of $\mathbb{Q}((t))$ into $K((t))$, of the subfield `modularFunctionFieldFull N` of $\mathbb{Q}((t))$ generated over $\mathbb{Q}$ by the expansions `divisorExpansions N`. A place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring; a divisor is a finitely supported function $D$ from places to $\mathbb{Z}$, its degree is $\sum_v D(v)\cdot \deg v$, and the Riemann–Roch space `riemannRochSpace D` is the $K$-submodule of those $f \in F$ with $v(f) \le \exp(D(v))$ for every place $v$, where $v(\cdot)$ is the $\mathbb{Z}^{m0}$-valued adic valuation attached to $v$ — i.e. the usual condition $\operatorname{ord}_v(f) \ge -D(v)$, written multiplicatively. The assertion is that there exists a natural number $g_0$, depending only on $N$, such that for every divisor $D$ with $g_0 \le \deg D$ and every place $v$ there is a $u \in$ `riemannRochSpace D` with $u \notin$ `riemannRochSpace (D - Finsupp.single v 1)`, the latter divisor being $D$ with its coefficient at $v$ lowered by one. Equivalently, for $\deg D$ large the inclusion $L(D - v) \subseteq L(D)$ is strict, so some $u \in L(D)$ has order exactly $-D(v)$ at $v$.
--
--   This is the standard consequence of Riemann–Roch that on a curve every divisor of sufficiently large degree admits a function with prescribed exact pole order at any given place, here for the function field of the modular curve of level $N$ over $\overline{\mathbb{Q}}$, with a degree bound uniform in the divisor and the place. It is used in the construction of models and of prolongations of places on the modular curve, for instance by [`ModularCurve.JZero.quot_rep`](thm.html#ModularCurve.JZero.quot_rep) and by the existence statement [`ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed), to produce a function whose order at a prescribed place is exactly zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_mem_riemannRochSpace_notMem_sub_single_of_le_degree (N : ℕ) [NeZero N] :
    ∃ g₀ : ℕ, ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g₀ : ℤ) ≤ Divisor.degree D →
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        ∃ u ∈ riemannRochSpace D, u ∉ riemannRochSpace (D - Finsupp.single v (1 : ℤ)) := by sorry
