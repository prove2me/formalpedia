-- Prove2me | Theorems.Thm_ModularCurve_exists_iterate_qExpFrobeniusPushforwardModL_eq_self_of_forall_pow_eq_self
-- name    : ModularCurve.exists_iterate_qExpFrobeniusPushforwardModL_eq_self_of_forall_pow_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/84c58d00-42dc-585d-a5b4-5f0e475d7e89
-- title:
--   Frobenius-periodicity of all divisor classes of ̄ F'
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and hypotheses $p \mid M$, $p^2 \nmid M$, together with $M/p \neq 0$. Let $\kappa$ be an algebraically closed field of characteristic $p$ such that every $a \in \kappa$ satisfies $a^{p^n} = a$ for some $n > 0$ (so $\kappa$ is algebraic over $\mathbb{F}_p$). Write $\bar F' =$ `Fbar p M H hpM κ` for the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)` attached to the subgroup `ΓN p M H hpM` of $\mathrm{SL}_2(\mathbb{Z})$, and let $\mathrm{Pic}^0_\kappa(\bar F')$ be the quotient of the group of degree-zero divisors — finitely supported $\mathbb{Z}$-valued functions on the places of $\bar F'$ over $\kappa$ — by the subgroup of principal divisors. Let $F$ be an additive endomorphism of $\mathrm{Pic}^0_\kappa(\bar F')$ that agrees pointwise with `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p` (the Frobenius push-forward map when its input predicate `QExpFrobeniusInputsModL` holds, and the zero map otherwise). Then for every class $z \in \mathrm{Pic}^0_\kappa(\bar F')$ there is $j > 0$ with $F^{j}(z) = z$.
--
--   This is the statement that, over an algebraic closure of $\mathbb{F}_p$, every divisor class on the reduction of the modular curve of level `ΓN p M H hpM` is defined over a finite field, hence periodic under the Frobenius push-forward. It is used to deduce that the relevant Picard group consists of elements of finite additive order, in [`ModularCurve.isOfFinAddOrder_pic0_fbar_of_forall_pow_eq_self`](thm.html#ModularCurve.isOfFinAddOrder_pic0_fbar_of_forall_pow_eq_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_iterate_qExpFrobeniusPushforwardModL_eq_self_of_forall_pow_eq_self.lean

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

theorem ModularCurve.exists_iterate_qExpFrobeniusPushforwardModL_eq_self_of_forall_pow_eq_self
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (halg : ∀ a : κ, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (F : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p z)
    (z : Pic0 κ (Fbar p M H hpM κ)) : ∃ j : ℕ, 0 < j ∧ (⇑F)^[j] z = z := by sorry
