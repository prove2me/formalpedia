-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_resFnFun_add_of_mem
-- name    : ModularCurve.SSHeckeV2.resFnFun_add_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/8fc3c59d-4278-53db-bb0b-5c80bd20eaa6
-- title:
--   Additivity of the supersingular residue map on L(D_m)
-- statement:
--   Fix a prime $p$ with $5 \le p$ and an algebraically closed field $K$ of characteristic $p$ (with decidable equality), and a nonzero natural number $N$ whose image in $K$ is nonzero; fix $m \ge 1$. Let $G$ and $G'$ be elements of the modular function field `modularFunctionFieldC K N`, the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the two $j$-series `jqModC K` and `jqNModC K N`, and assume both lie in `riemannRochSpace (weightDivisor K N m)`, i.e. that for every place $v$ of this function field over $K$ the adic valuation of the element is at most $\exp$ of the value at $v$ of the divisor `weightDivisor K N m` (the divisor whose value at each place is the integer `weightFloor K N m`, when such a divisor exists, and $0$ otherwise). The conclusion is that `resFnFun p N K hp5 m` is additive on these two elements: as functions on the index type `SSIndex p N K hp5 (2 * (m : ℤ))`, for every index $x$ with underlying place $x.1$, the residue at $x.1$ of $\pi_{x}^{a}\,(G+G')$ equals the sum of the residues of $\pi_{x}^{a}G$ and $\pi_{x}^{a}G'$, where $\pi_x$ is `unif N K x.1` and $a$ is `poleOrder p N K hp5 (2m) x`.
--
--   This is the additivity half of the statement that taking leading coefficients at the supersingular index places is a $K$-linear map from the Riemann–Roch space of the weight-$m$ divisor to the carrier type of weight-$2m$ supersingular functions; together with the companion homogeneity statement it makes the residue map linear. It is used in the assembly of [`ModularCurve.SSHeckeV2.ssHeckeFun_window`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_window).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_resFnFun_add_of_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.resFnFun_add_of_mem
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m) (G G' : ↥(modularFunctionFieldC K N))
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m))
    (hG' : G' ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m)) :
    ModularCurve.resFnFun p N K hp5 m (G + G') = ModularCurve.resFnFun p N K hp5 m G + ModularCurve.resFnFun p N K hp5 m G' := by sorry
