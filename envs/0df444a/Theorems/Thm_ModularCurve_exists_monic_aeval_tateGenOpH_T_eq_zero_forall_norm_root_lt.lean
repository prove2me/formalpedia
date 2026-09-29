-- Prove2me | Theorems.Thm_ModularCurve_exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt
-- name    : ModularCurve.exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/3883e62c-0bd8-5518-80e3-3d0c2075645d
-- title:
--   Integral monic polynomial annihilating Tₚ on Tₚ J_H(N)
-- statement:
--   Let $N$ be a non-zero natural number, $p$ a prime not dividing $N$, $H$ a subgroup of $(\mathbb{Z}/N)^{\times}$, and $S$ a set of natural numbers with $p \notin S$. Assume the input predicate [`ModularCurve.HeckeDiamondInputsHAll N H`](def/ModularCurve_XHOperators.html#L113), that is: for every prime $\ell$ the predicate `HeckeInputsHAlong` holds for $\mathrm{AlgebraicClosure}\,\mathbb{Q}$, $N$, $H$, $\ell$ — the existence of the Hecke correspondence data at $\ell$ (that $\beta$ is defined, that $\alpha$ and $\beta$ are integral over the algebraic closure, that the relevant Laurent base change has principal divisors, and that $\alpha$ is finite along the map), together with the fundamental identity for $\beta$ and the norm formula for $\alpha$; and, for every $d \in (\mathbb{Z}/N)^{\times}$, the existence of an automorphism $\sigma$ of `xHFunctionFieldBar N H` over $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ satisfying `IsDiamondAutHBar N H d`, i.e. realising the diamond operator $\langle d\rangle$ on $q$-expansion quotients of integral modular forms of level $\Gamma_H(N)$. Then there is a monic $P \in \mathbb{Z}[X]$ such that $P$ annihilates the $\mathbb{Z}_p$-linear endomorphism [`ModularCurve.tateGenOpH N H S p (.T p _ hpS hpN)`](def/ModularCurve_XHOperators.html#L99) of the Tate module $T_p(J_H(N))$ — the group of sequences $(x_n)$ in $J_H(N)$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, with $T_p$ acting through `heckeOperatorHAlong` — and such that every complex root $z$ of $P$ satisfies $\|z\| < p+1$.
--
--   This is the Eichler–Shimura transfer of the Ramanujan–Petersson bound for weight-two eigenforms to the $p$-adic Tate module: the characteristic polynomial of $T_p$ on the integral homology of $X_H(N)$ is monic over $\mathbb{Z}$, kills $T_p$ on $T_p J_H(N)$, and has all complex roots of absolute value less than $p+1$. It feeds [`ModularCurve.sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia`](thm.html#ModularCurve.sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia), which rules out the eigenvalue relation $a_p^2 = (p+1)^2\langle p\rangle$ needed in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_monic_aeval_tateGenOpH_T_eq_zero_forall_norm_root_lt
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) (H : Subgroup (ZMod N)ˣ)
    (S : Set ℕ) (hpS : p ∉ S)
    (hin : ModularCurve.HeckeDiamondInputsHAll N H) :
    ∃ P : Polynomial ℤ, P.Monic ∧
      Polynomial.aeval (ModularCurve.tateGenOpH N H S p (.T p Fact.out hpS hpN)) P = 0 ∧
      ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ < (p + 1 : ℕ) := by sorry
