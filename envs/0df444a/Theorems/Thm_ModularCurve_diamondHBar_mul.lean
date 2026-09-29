-- Prove2me | Theorems.Thm_ModularCurve_diamondHBar_mul
-- name    : ModularCurve.diamondHBar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/990bf698-b5da-51f9-88bd-5c2b876a197d
-- title:
--   Multiplicativity of the diamond operators on J_H
-- statement:
--   Let $M$ be a positive integer and $H$ a subgroup of $(\mathbb{Z}/M)^\times$. Write $\bar F =$ `xHFunctionFieldBar M H` for the intermediate field of the Laurent series field $\overline{\mathbb{Q}}((q))$ over $\overline{\mathbb{Q}}$ obtained by base change along $\overline{\mathbb{Q}}$ of the $q$-expansion function field `xHFunctionField M H`, and let $J_H =$ [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127) be the group `Pic0` of that field over $\overline{\mathbb{Q}}$, i.e. the degree-zero divisors of $\bar F/\overline{\mathbb{Q}}$ modulo the subgroup of principal divisors. For a unit $d$ of $\mathbb{Z}/M$, `diamondAutHBar M H d` is the $\overline{\mathbb{Q}}$-algebra automorphism of $\bar F$ chosen to satisfy the predicate `IsDiamondAutHBar M H d`, if such an automorphism exists, and the identity otherwise; `diamondHBar M H d` is the additive endomorphism of $J_H$ obtained from the semilinear automorphism $(\,\cdot\,,1)$ attached to it via `SemilinearAut.ofAlgAut`, acting on divisor classes. The assertion is that for all units $d, d'$ of $\mathbb{Z}/M$ and every $x \in J_H$, $$\langle d d'\rangle_* x = \langle d\rangle_*\bigl(\langle d'\rangle_* x\bigr),$$ where $\langle\,\cdot\,\rangle_*$ denotes `diamondHBar M H`. The statement is pointwise multiplicativity only; it does not assert that $\langle 1 \rangle_*$ is the identity or record the map as a monoid homomorphism.
--
--   This is the composition law for the covariant diamond operators on the Jacobian of $X_H(M)$ in the $q$-expansion model, the half of the statement that $d \mapsto \langle d \rangle_*$ is an action of $(\mathbb{Z}/M)^\times$ on $J_H$. It is used in the construction of Hecke actions on $J_H$ and of Galois-stable Hecke lattices, and in the verification of the commutation and Eichler–Shimura type relations between Hecke, diamond and Frobenius operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondHBar_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.diamondHBar_mul (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (d d' : (ZMod M)ˣ) (x : ModularCurve.JH M H) :
    ModularCurve.diamondHBar M H (d * d') x =
      ModularCurve.diamondHBar M H d (ModularCurve.diamondHBar M H d' x) := by sorry
