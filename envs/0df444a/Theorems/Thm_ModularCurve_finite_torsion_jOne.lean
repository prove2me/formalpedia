-- Prove2me | Theorems.Thm_ModularCurve_finite_torsion_jOne
-- name    : ModularCurve.finite_torsion_jOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/29902918-889b-5fe4-ab01-b4033b33e00e
-- title:
--   Finiteness of the n-torsion of J₁(M) over ℚ̄
-- statement:
--   Let $M$ be a natural number with $M \neq 0$ and let $n$ be a natural number with $n \neq 0$. Write $\overline{\mathbb{Q}}$ for `AlgebraicClosure ℚ` and let $F =$ [`ModularCurve.x1FunctionFieldBar M`](def/ModularCurve_X1.html#L182) be the intermediate field of $\overline{\mathbb{Q}}((t))$ (Laurent series over $\overline{\mathbb{Q}}$) generated over $\overline{\mathbb{Q}}$ by the image, under the coefficientwise embedding of $\mathbb{Q}((t))$ into $\overline{\mathbb{Q}}((t))$, of the function field [`ModularCurve.x1FunctionFieldC ℚ M`](def/ModularCurve_X1.html#L134) of $X_1(M)$ over $\mathbb{Q}$. For this extension $\overline{\mathbb{Q}} \subseteq F$ form the group of divisors, the finitely supported functions from the places of $F$ over $\overline{\mathbb{Q}}$ to $\mathbb{Z}$, its subgroup `Divisor.degZero` of divisors in the kernel of the degree map, and the subgroup `Divisor.principal` of divisors of the form $\mathrm{ord}_v(f)$ for a nonzero $f \in F$; then $\mathrm{Pic}^0 =$ `Pic0 ℚ̄ F` is the quotient of the degree-zero divisors by the principal ones lying in it. The assertion is that the subgroup of elements $x$ of this $\mathrm{Pic}^0$ with $n \cdot x = 0$ (the $\mathbb{Z}$-torsion-by-$n$ submodule, as an additive subgroup) is a finite type.
--
--   This is the finiteness of the $n$-torsion of the Jacobian $J_1(M)$ over $\overline{\mathbb{Q}}$, realised divisor-theoretically as the degree-zero divisor class group of the function field of $X_1(M)$ base changed to $\overline{\mathbb{Q}}$; only finiteness is asserted, with no count of the order. It is used in the study of torsion in the Jacobian of $X_1$ attached to a prime, in particular in bounding the cardinality of inertia invariants of torsion subgroups by counting points over valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_torsion_jOne.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.finite_torsion_jOne (M : ℕ) [NeZero M] (n : ℕ) (hn : n ≠ 0) :
    Finite (Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar M) n) := by sorry
