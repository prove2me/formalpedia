-- Prove2me | Theorems.Thm_ModularCurve_tateModule_eq_zero_of_forall_heckeOperatorBar_heckeOperatorBar_eq_smul
-- name    : ModularCurve.tateModule_eq_zero_of_forall_heckeOperatorBar_heckeOperatorBar_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/b6a83336-d743-53d0-8bd8-799e1e34764b
-- title:
--   Tate modules have no Tₚ²=(p+1)² eigenvectors
-- statement:
--   Let $N_0$ be a nonzero natural number, let $p$ be a prime that does not divide $N_0$, and let $q$ be a prime with $q \neq p$. Write $J_0(N_0)$ for `JZero N₀`, the group of degree-zero divisor classes — degree-zero divisors modulo principal divisors — of the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N_0$, and let $T_p =$ `heckeOperatorBar N₀ ⟨p, hp⟩` be the $\mathbb{Z}$-linear endomorphism of $J_0(N_0)$ obtained from the Hecke correspondence at $p$ over $\overline{\mathbb{Q}}$. The assertion is that every element $x$ of the $q$-adic Tate module [`TateModule q (JZero N₀)`](def/EllipticCurve_TateModule.html#L15) — that is, every sequence $x \colon \mathbb{N} \to J_0(N_0)$ satisfying $q^n \cdot x_n = 0$ and $q \cdot x_{n+1} = x_n$ for all $n$ — such that each component satisfies $T_p(T_p(x_n)) = (p+1)^2 \cdot x_n$ (integer scalar multiplication) is the zero element. Equivalently, $T_p^2 - (p+1)^2$ annihilates no nonzero element of this Tate module.
--
--   This is the form in which the Eichler–Shimura relation at a prime $p$ of good reduction is used: the quadratic relation forces the Frobenius at $p$ to act on a Tate module vector either with $\sigma^2$ trivial or through multiplication by $\pm p$, and in both cases the vector vanishes. It is cited by [`ModularCurve.exists_pow_smul_eq_zero_of_heckeOperatorBar_heckeOperatorBar_eq_smul`](thm.html#ModularCurve.exists_pow_smul_eq_zero_of_heckeOperatorBar_heckeOperatorBar_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tateModule_eq_zero_of_forall_heckeOperatorBar_heckeOperatorBar_eq_smul.lean

import Definitions.Def_ModularCurve_JZeroNeronData
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.tateModule_eq_zero_of_forall_heckeOperatorBar_heckeOperatorBar_eq_smul
    (N₀ p : ℕ) [NeZero N₀] (hp : p.Prime) (hpN₀ : ¬ p ∣ N₀) (q : ℕ) [Fact q.Prime] (hqp : q ≠ p) :
    ∀ x : _root_.TateModule q (JZero N₀),
      (∀ n : ℕ, heckeOperatorBar N₀ ⟨p, hp⟩ (heckeOperatorBar N₀ ⟨p, hp⟩ ((x : ℕ → JZero N₀) n)) =
        (((p : ℤ) + 1) ^ 2) • (x : ℕ → JZero N₀) n) → x = 0 := by sorry
