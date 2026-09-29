-- Prove2me | Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem
-- name    : ModularCurve.diamondHBar_apply_eq_self_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/055cf033-6d05-52b9-b2bb-0408629d6b94
-- title:
--   Diamond operators ⟨ d⟩ with d∈ H act trivially on J_H
-- statement:
--   Fix a natural number $M$ (nonzero) and a subgroup $H$ of $(\mathbb{Z}/M)^\times$. Let $\overline{\mathbb{Q}}$ be the chosen algebraic closure of $\mathbb{Q}$ and let [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) be the base change to $\overline{\mathbb{Q}}$, inside the Laurent series field $\overline{\mathbb{Q}}((q))$, of the function field of $X_H(M)$; write [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127) for the associated group $\operatorname{Pic}^0$, namely the group of degree-zero divisors of this $\overline{\mathbb{Q}}$-function field modulo the subgroup of principal divisors. For a unit $d$ of $\mathbb{Z}/M$, [`ModularCurve.diamondAutHBar M H d`](def/ModularCurve_XHOperators.html#L32) is the $\overline{\mathbb{Q}}$-algebra automorphism of [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) obtained by choosing, if one exists, an automorphism satisfying the predicate [`ModularCurve.IsDiamondAutHBar M H d`](def/ModularCurve_XHOperators.html#L18), and the identity automorphism otherwise; [`ModularCurve.diamondHBar M H d`](def/ModularCurve_XHOperators.html#L57) is the endomorphism of the additive group [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127) induced by the action of the corresponding $\overline{\mathbb{Q}}$-semilinear automorphism (the pair consisting of this automorphism and the identity of $\overline{\mathbb{Q}}$) on divisor classes. The assertion is: if $d \in H$, then for every $x \in$ [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127) one has $\langle d\rangle x = x$.
--
--   This records that the diamond operators on the Jacobian of $X_H(M)$ over $\overline{\mathbb{Q}}$ are trivial on the subgroup $H$, so that the diamond action factors through $(\mathbb{Z}/M)^\times/H$. It is used in the analysis of the Hecke and Frobenius action on the Néron fibres of $J_H$ at a prime and in the computation of the inertia action in the cyclotomic pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.diamondHBar_apply_eq_self_of_mem
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ) (hd : d ∈ H) (x : ModularCurve.JH M H) :
    ModularCurve.diamondHBar M H d x = x := by sorry
