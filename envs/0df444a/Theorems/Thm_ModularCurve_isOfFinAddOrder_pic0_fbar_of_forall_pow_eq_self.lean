-- Prove2me | Theorems.Thm_ModularCurve_isOfFinAddOrder_pic0_fbar_of_forall_pow_eq_self
-- name    : ModularCurve.isOfFinAddOrder_pic0_fbar_of_forall_pow_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/3e812dd4-42a3-53ee-8ea2-9554c33536ad
-- title:
--   Torsion of Pic⁰ over an algebraic closure of mathbb Fₚ
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ but $p^2 \nmid M$ (and $M/p$ nonzero), together with a subgroup $H$ of $(\mathbb Z/M)^\times$. Let $\kappa$ be an algebraically closed field of characteristic $p$ such that every $a \in \kappa$ satisfies $a^{p^n} = a$ for some $n > 0$, i.e. $\kappa$ is algebraic over $\mathbb F_p$. Write $\bar F =$ `Fbar p M H hpM κ` for the underlying type of the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)` over $\kappa$, attached to the congruence subgroup `ΓN p M H hpM` determined by these data. The assertion is that every element $z$ of `Pic0 κ` $\bar F$ — that is, of the quotient of the group of degree-zero divisors (finitely supported $\mathbb Z$-valued functions on the places of $\bar F$ over $\kappa$ whose degree vanishes) by the subgroup of principal divisors lying in it — has finite additive order: some positive multiple of $z$ is zero.
--
--   This is the statement that the Jacobian of a curve over an algebraic closure of a finite field is a torsion group, in the divisor-class-group formulation for the $q$-expansion function field of the relevant modular curve in characteristic $p$ at level dividing $M$ exactly once. It is used in the analysis of the reduction of the Jacobian at $p$, feeding into [`ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self`](thm.html#ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isOfFinAddOrder_pic0_fbar_of_forall_pow_eq_self.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

theorem ModularCurve.isOfFinAddOrder_pic0_fbar_of_forall_pow_eq_self
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (halg : ∀ a : κ, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (z : Pic0 κ (Fbar p M H hpM κ)) : IsOfFinAddOrder z := by sorry
