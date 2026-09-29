-- Prove2me | Theorems.Thm_ModularCurve_JH_exists_tateModule_proj_eq_of_mem_torsionBy
-- name    : ModularCurve.JH.exists_tateModule_proj_eq_of_mem_torsionBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/fb1b5514-af90-5206-ae6b-1db4b6616a1a
-- title:
--   Surjectivity of the level-n map TₚJ_H → J_H[pⁿ]
-- statement:
--   Fix $M \in \mathbb{N}$ with $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, a prime $p$ and an exponent $n \in \mathbb{N}$. Write $J =$ [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127) for the degree-zero divisor class group $\mathrm{Pic}^0$ of the function field `xHFunctionFieldBar M H` — the base change to $\overline{\mathbb{Q}}$ (an algebraic closure of $\mathbb{Q}$) of the function field of $X_H(M)$, realised inside Laurent series — that is, degree-zero divisors modulo principal divisors, regarded as an additive group. The assertion is: for every $m \in J$ lying in the $\mathbb{Z}$-torsion submodule $\mathrm{torsionBy}\,(p^n)$, i.e. satisfying $p^n \cdot m = 0$, there exists an element $x$ of [`TateModule p J`](def/EllipticCurve_TateModule.html#L15) — by definition a sequence $(x_k)_{k \in \mathbb{N}}$ of elements of $J$ such that $p^k \cdot x_k = 0$ and $p \cdot x_{k+1} = x_k$ for all $k$ — whose $n$-th component, i.e. the image of $x$ under the evaluation homomorphism [`TateModule.proj p J n`](def/EllipticCurve_TateModule.html#L122), equals $m$.
--
--   This is the surjectivity of the level-$n$ projection from the $p$-adic Tate module of the Jacobian $J_H(M)$ onto its $p^n$-torsion, a consequence of divisibility of the group of $\overline{\mathbb{Q}}$-points of the Jacobian. It is used to transport a $p$-power torsion class into the image of the Tate module in the counting arguments for the ordinary corner of the Hecke module attached to $X_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JH_exists_tateModule_proj_eq_of_mem_torsionBy.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JH.exists_tateModule_proj_eq_of_mem_torsionBy
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ m ∈ Submodule.torsionBy ℤ (ModularCurve.JH M H) ((p ^ n : ℕ) : ℤ),
      ∃ x : TateModule p (ModularCurve.JH M H), TateModule.proj p (ModularCurve.JH M H) n x = m := by sorry
