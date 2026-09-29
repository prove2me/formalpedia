-- Prove2me | Theorems.Thm_ModularCurve_exists_pow_smul_eq_zero_of_forall_tateModule_eq_zero
-- name    : ModularCurve.exists_pow_smul_eq_zero_of_forall_tateModule_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/62b3c9fd-a0a2-54f9-b438-fd3db5674eeb
-- title:
--   Bounded exponent on p-power torsion from Tate module vanishing
-- statement:
--   Let $N_0$ be a nonzero natural number, let $p$ be a prime, and let $q$ be a prime. Write $J =$ `JZero N₀` for the degree-zero divisor class group $\mathrm{Pic}^0$ of the level-$N_0$ modular function field after base change to an algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$, and write $T =$ `heckeOperatorBar N₀ ⟨p, hp⟩` for the $\mathbb{Z}$-linear endomorphism of $J$ obtained from `heckeOperatorAlong` over $\overline{\mathbb{Q}}$ at level $N_0$ and index $p$. The hypothesis is that the $q$-adic Tate module [`TateModule q (JZero N₀)`](def/EllipticCurve_TateModule.html#L15) — the group of sequences $x : \mathbb{N} \to J$ with $q^n \cdot x_n = 0$ and $q \cdot x_{n+1} = x_n$ for all $n$ — contains no nonzero element all of whose components satisfy $T(T(x_n)) = (p+1)^2 \cdot x_n$. The conclusion is that there exists $e \in \mathbb{N}$ such that for every $k \in \mathbb{N}$ and every $y \in J$ killed by $p^k$ (that is, lying in the $\mathbb{Z}$-torsion submodule `jZeroTorsion N₀ (p ^ k)` of elements with $(p^k) \cdot y = 0$) and satisfying $T(T(y)) = (p+1)^2 \cdot y$, one has $p^e \cdot y = 0$. No relation between $q$ and $p$ or $N_0$ is assumed.
--
--   This is the uniform-boundedness step which converts the vanishing of the kernel of $T_p^2 - (p+1)^2$ on a single $\ell$-adic Tate module of $J_0(N_0)$ into a single exponent $p^e$ annihilating that kernel on all $p$-power torsion, the point being that the characteristic polynomial of a correspondence is one monic integer polynomial of degree $2g$ realised on every Tate module. It is used by [`ModularCurve.exists_pow_smul_eq_zero_of_heckeOperatorBar_heckeOperatorBar_eq_smul`](thm.html#ModularCurve.exists_pow_smul_eq_zero_of_heckeOperatorBar_heckeOperatorBar_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pow_smul_eq_zero_of_forall_tateModule_eq_zero.lean

import Definitions.Def_ModularCurve_JZeroNeronData
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_pow_smul_eq_zero_of_forall_tateModule_eq_zero
    (N₀ p : ℕ) [NeZero N₀] (hp : p.Prime) (q : ℕ) [Fact q.Prime]
    (hinj : ∀ x : _root_.TateModule q (JZero N₀),
      (∀ n : ℕ, heckeOperatorBar N₀ ⟨p, hp⟩ (heckeOperatorBar N₀ ⟨p, hp⟩ ((x : ℕ → JZero N₀) n)) =
        (((p : ℤ) + 1) ^ 2) • (x : ℕ → JZero N₀) n) → x = 0) :
    ∃ e : ℕ, ∀ (k : ℕ) (y : JZero N₀), y ∈ jZeroTorsion N₀ (p ^ k) →
      heckeOperatorBar N₀ ⟨p, hp⟩ (heckeOperatorBar N₀ ⟨p, hp⟩ y) = (((p : ℤ) + 1) ^ 2) • y →
        p ^ e • y = 0 := by sorry
