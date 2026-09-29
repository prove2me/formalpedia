-- Prove2me | Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
-- name    : ModularCurve.diamondAutHBar_mul_and_diamondAutHBar_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/3fed6ac0-ab33-59d9-ba34-8841dee475b0
-- title:
--   Multiplicativity of the diamond automorphisms ⟨ d⟩^*
-- statement:
--   Let $M$ be a natural number with $M \neq 0$ and let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$. For $d \in (\mathbb{Z}/M)^\times$, `diamondAutHBar M H d` is the automorphism of the intermediate field $\overline{\mathbb{Q}}\cdot F(\Gamma_H(M)) =$ `xHFunctionFieldBar M H` of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ over $\overline{\mathbb{Q}}$ obtained by choosing, when one exists, an $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ with the property `IsDiamondAutHBar M H d`: for every weight $k$, every pair of modular forms $f,g$ of weight $k$ on $\Gamma_H(M)$ with integral $q$-expansions $p_f, p_g$ such that the rational Laurent series attached to $p_g$ is nonzero, and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ with $\gamma_{00} \equiv d \pmod M$, there is a Laurent series $y$ over $\mathbb{Q}$ belonging to $F(\Gamma_H(M))$ with $\sigma$ sending the image under `coeffEmb` of the ratio attached to $p_f/p_g$ to the image of $y$, and with $y$, pushed to $\mathbb{C}$, times the $q$-expansion of $g\mid_k\gamma$ equal to the $q$-expansion of $f\mid_k\gamma$; failing existence, the identity is taken. The theorem asserts, unconditionally, the two monoid-homomorphism identities: $\langle ab\rangle^* = \langle a\rangle^*\,\langle b\rangle^*$ (composition of automorphisms) for all $a,b \in (\mathbb{Z}/M)^\times$, and $\langle 1\rangle^* = \mathrm{id}$.
--
--   This is the statement that the diamond operators $\langle d\rangle$ act on the function field of $X_H(M)$ over $\overline{\mathbb{Q}}$ through a homomorphism of $(\mathbb{Z}/M)^\times$, so that the chosen automorphisms assemble into a group action. It is used in the study of the model of $X_H$ at $p$ and its reductions, and in compatibility statements between diamond automorphisms and other field automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve

theorem ModularCurve.diamondAutHBar_mul_and_diamondAutHBar_one (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (∀ a b : (ZMod M)ˣ, diamondAutHBar M H (a * b) = diamondAutHBar M H a * diamondAutHBar M H b) ∧
      diamondAutHBar M H 1 = 1 := by sorry
