-- Prove2me | Theorems.Thm_ModularCurve_stackOrd_nonneg_and_le_ord_of_isModPFormFn
-- name    : ModularCurve.stackOrd_nonneg_and_le_ord_of_isModPFormFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/6be703bb-be18-5b5d-9edb-260194290430
-- title:
--   Integrality bounds stack orders and orders at cusps
-- statement:
--   Let $p\ge 5$ be a prime, let $N\ge 1$ with $p\nmid N$, and let $K$ be an algebraically closed field of characteristic $p$. Let $m$ be a natural number and let $G$ be a nonzero element of the level-$N$ geometric modular function field `modularFunctionFieldC K N`, the intermediate field of $K((q))$ generated over $K$ by $\bar j(q)$ = `jqModC K` (the Laurent series $q^{-1}$ times the reduction of the power series $j$-numerator) and by $\bar j(q^N)$ = `jqNModC K N`, its image under $q\mapsto q^N$. Assume `IsModPFormFn K m` holds for $G$ viewed in $K((q))$, i.e. $G^6\,\bar j^{4m}(\bar j-1728)^{3m}$ is integral over $K[\bar j]$ and $G^2\,\bar j^{m}(\bar j-1728)^{m}$ is integral over $K[\bar j^{-1}]$. Then two assertions hold. First, for every place $x$ of `modularFunctionFieldC K N` over $K$ (a proper valuation subring containing $K$ whose ideals are principal) that is affine in the sense that both $\bar j$ and $\bar j(q^N)$ lie in its valuation ring, one has $0\le \mathrm{stackOrd}_N(m,G,x)$, where this quantity is $\lfloor w(x)/r_x\rfloor\cdot \mathrm{ord}_x G + m\,(w(x)-1)$ with $w(x)=$ `jWidth` of the residue value $x(\bar j)$, equal to $3$ if that value is $0$, to $2$ if it is $1728$ and to $1$ otherwise, $r_x =$ `placeRamificationJ N x`, and the quotient taken as natural-number division. Second, for every place $x$ with $\mathrm{ord}_x \bar j<0$ one has $m\cdot(-\mathrm{ord}_x\bar j)\le \mathrm{ord}_x G$.
--
--   This is one direction of the dictionary between the description of mod $p$ modular functions of weight $2m$ by integrality of $G^6\bar j^{4m}(\bar j-1728)^{3m}$ and $G^2\bar j^m(\bar j-1728)^m$, and their description by orders at the places of the level-$N$ function field: integrality forces non-negative order on the moduli stack at affine places and vanishing to order at least $m$ times the pole order of $\bar j$ at the cusps. It is used in the construction of mod $p$ Hecke eigenforms from Riemann–Roch spaces and in the congruence statements for $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_stackOrd_nonneg_and_le_ord_of_isModPFormFn.lean

import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.stackOrd_nonneg_and_le_ord_of_isModPFormFn
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (m : ℕ) (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (hG : IsModPFormFn K m (G : LaurentSeries K)) :
    (∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x →
        0 ≤ stackOrd N (m : ℤ) G x) ∧
    (∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
        (m : ℤ) * (-(x.ord (jGeomGen K N))) ≤ x.ord G) := by sorry
