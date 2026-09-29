-- Prove2me | Theorems.Thm_ModularCurve_resFnFun_eq_zero_iff_forall_one_le_stackOrd
-- name    : ModularCurve.resFnFun_eq_zero_iff_forall_one_le_stackOrd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/6a5005e9-19a8-5cdd-9a42-2fadcd8e766e
-- title:
--   Vanishing supersingular leading coefficients versus stack order
-- statement:
--   Let $p$ be a prime with $5\le p$, let $K$ be an algebraically closed field of characteristic $p$ (with decidable equality), let $N\ge 1$ be an integer whose image in $K$ is nonzero, and let $m$ be a natural number with $1\le m$. Let $F=$ `modularFunctionFieldC K N`, the intermediate field of the Laurent series field over $K$ generated over $K$ by `jqModC K` and `jqNModC K N` (the $q$-expansions of $j$ and of $j$ at level $N$), and let $G\in F$ be nonzero and lie in the Riemann–Roch space of the divisor `weightDivisor K N m`, i.e. for every place $x$ of $F$ over $K$ (a proper valuation subring of $F$ containing $K$ and a principal ideal ring) the adic valuation of $G$ at $x$ is at most $\exp$ of the coefficient of `weightDivisor K N m` at $x$. Then the function `resFnFun p N K hp5 m G`, which sends an index $x$ to `lead N K x.1 (poleOrder p N K hp5 (2 * m) x) G`, is identically zero on the index type `SSIndex p N K hp5 (2 * m)` — the places $x$ lying in `ssPlaces p N K` with $2\mid 2m$, $2\le 2m$, `placeWidth N x` dividing $m$, and $5\le p$ — if and only if for every such $x$ one has $$1\le \mathrm{stackOrd}= (\mathrm{placeWidth}\,N\,x)\cdot \operatorname{ord}_x(G) + m\bigl(\mathrm{jWidth}(x(\,j\,))-1\bigr),$$ where $x(\,j\,)$ is the value at $x$ of the generator `jGeomGen K N` and `jWidth` is $3$ at $0$, $2$ at $1728$ and $1$ elsewhere.
--
--   This is the function-field form of the statement that a mod $p$ modular form of weight $2m$ whose leading coefficients at all supersingular points vanish has positive order there, i.e. is divisible by the Hasse invariant; the right-hand side records that order on the moduli stack, with the local width factors. It is used in the analysis of the supersingular Hecke module, in [`ModularCurve.SSHeckeV2.mem_modPMod_sub_of_resQFun_eq_zero`](thm.html#ModularCurve.SSHeckeV2.mem_modPMod_sub_of_resQFun_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_resFnFun_eq_zero_iff_forall_one_le_stackOrd.lean

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.resFnFun_eq_zero_iff_forall_one_le_stackOrd
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m) (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m)) :
    ModularCurve.resFnFun p N K hp5 m G = 0 ↔
      ∀ x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)), 1 ≤ stackOrd N (m : ℤ) G x.1 := by sorry
