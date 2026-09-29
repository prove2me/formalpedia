-- Prove2me | Theorems.Thm_ModularCurve_finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL
-- name    : ModularCurve.finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/2bddd85a-0d5f-5bde-8c83-f4aa3ec2014b
-- title:
--   Finiteness of Frobenius-fixed divisor classes on ̄ F in characteristic p
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and hypotheses $p \mid M$ and $p^2 \nmid M$ (with $M/p$ nonzero). Let $\kappa$ be an algebraically closed field of characteristic $p$ such that every $a \in \kappa$ satisfies $a^{p^n} = a$ for some $n > 0$, i.e. $\kappa$ is algebraic over $\mathbb{F}_p$. Write $\bar F =$ `Fbar p M H hpM κ` for the function field $\kappa$-algebra `qExpFunctionFieldC κ (ΓN p M H hpM)`, the intermediate field of Laurent series over $\kappa$ attached to the level group `ΓN p M H hpM`, and let $\mathrm{Pic}^0$ denote the quotient of the group of degree-zero divisors on places of $\bar F$ over $\kappa$ (finitely supported $\mathbb{Z}$-valued functions of degree zero) by the subgroup of principal divisors. Let $F$ be an additive endomorphism of this $\mathrm{Pic}^0$ which agrees pointwise with `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p`, the map that is the Frobenius push-forward `qExpFrobeniusPic0PushforwardModL` when the input condition `QExpFrobeniusInputsModL κ (ΓN p M H hpM) p` holds and the zero map otherwise. Then for every $n > 0$ the set of fixed points of the $n$-fold iterate $F^{[n]}$ is finite.
--
--   This is the function-field form of the finiteness of the group of $\mathbb{F}_{p^n}$-rational points of the Jacobian: over a field algebraic over $\mathbb{F}_p$, the classes fixed by an iterate of the Frobenius push-forward are those rational over a finite subfield, and hence finitely many. It is the $\Gamma_H$-level instance of the general finiteness statement for curves, and is used by [`ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self`](thm.html#ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self), [`ModularCurve.finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self`](thm.html#ModularCurve.finite_setOf_diamond_qExpFrobeniusPushforwardModL_sq_eq_self) and [`ModularCurve.isOfFinAddOrder_pic0_fbar_of_forall_pow_eq_self`](thm.html#ModularCurve.isOfFinAddOrder_pic0_fbar_of_forall_pow_eq_self) in the analysis of the reduction of the Jacobian at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve.XHDRLevel
open AlgebraicCurve
open ModularCurve
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

theorem ModularCurve.finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (halg : ∀ a : κ, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (F : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p z)
    (n : ℕ) (hn : 0 < n) :
    (Function.fixedPoints (⇑F)^[n]).Finite := by sorry
