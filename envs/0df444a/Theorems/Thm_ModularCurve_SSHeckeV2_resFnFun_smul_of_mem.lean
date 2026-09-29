-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_resFnFun_smul_of_mem
-- name    : ModularCurve.SSHeckeV2.resFnFun_smul_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/3db30873-e917-5080-867e-e1b6d8aa48ac
-- title:
--   Homogeneity of the supersingular leading-coefficient map
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $K$ be an algebraically closed field of characteristic $p$, and let $N \ge 1$ be such that $N \ne 0$ in $K$. Let $m$ be a natural number with $1 \le m$, let $c \in K$, and let $G$ be an element of the modular function field `modularFunctionFieldC K N`, the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the $j$-series `jqModC K` and its $N$-fold expansion `jqNModC K N`. Assume $G$ lies in the Riemann–Roch space of the divisor `weightDivisor K N m`, i.e. $v(G) \le \exp(D(v))$ in $\mathbb{Z}^{m0}$ for every place $v$ of this field, where $D$ is a finitely supported divisor whose value at each place $w$ is the weight floor built from $\lfloor 2m\,\mathrm{ord}_w(j)/3\rfloor$, $\lfloor m\,\mathrm{ord}_w(j-1728)/2\rfloor$ and $m\,\mathrm{ord}_w(j)$ according to the signs of these orders (and $0$ if no such divisor exists). Then `resFnFun p N K hp5 m` is homogeneous at $G$: the function on the index type `SSIndex p N K hp5 (2m)` sending $x$ to $\mathrm{ev}_{x_1}\!\left(\pi_{x_1}^{\,a(x)}\,(c \cdot G)\right)$, with $\pi_{x_1}$ the chosen uniformiser at the place $x_1$ and $a(x)$ the pole order $\lfloor m(\mathrm{jWidth}-1)\rfloor$-type integer `poleOrder p N K hp5 (2*m) x`, equals $c$ times the corresponding function for $G$, pointwise.
--
--   This is the scalar-multiplication half of the assertion that the map sending a function in the Riemann–Roch space of the weight divisor to its tuple of leading coefficients at the supersingular places is $K$-linear; additivity is the companion statement. It is used in the construction of the Hecke action window [`ModularCurve.SSHeckeV2.ssHeckeFun_window`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_window).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_resFnFun_smul_of_mem.lean

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

theorem ModularCurve.SSHeckeV2.resFnFun_smul_of_mem
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m) (c : K) (G : ↥(modularFunctionFieldC K N))
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m)) :
    ModularCurve.resFnFun p N K hp5 m (c • G) = c • ModularCurve.resFnFun p N K hp5 m G := by sorry
