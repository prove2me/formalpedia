-- Prove2me | Theorems.Thm_ModularCurve_mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub
-- name    : ModularCurve.mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/69417f82-fad6-5176-a525-475c781087d9
-- title:
--   Cuspidal dictionary: L(D_{2m}-cusps) versus mod p cusp forms
-- statement:
--   Fix a prime $p\ge 5$, a nonzero level $N$ with $p\nmid N$, an algebraically closed field $K$ of characteristic $p$, and an integer $m\ge 1$. Let $F=\mathrm{modularFunctionFieldC}\ K\ N$ be the intermediate field of $\mathrm{LaurentSeries}\ K$ generated over $K$ by $\bar\jmath=\mathrm{jqModC}\ K=q^{-1}\cdot(\text{the }j\text{-numerator power series})$ and by its $N$-th $q$-expansion $\mathrm{jqNModC}\ K\ N$, and write $\bar\jmath$ also for the element $\mathrm{jGeomGen}\ K\ N\in F$. Let $E$ be a divisor of $F/K$, i.e. a finitely supported $\mathbb Z$-valued function on the places $w$ (valuation subrings of $F$ containing $K$, proper, with principal ideals), and assume that for every $w$ one has $E(w)=\mathrm{weightFloor}\ K\ N\ m\ w-1$ when $\mathrm{ord}_w\bar\jmath<0$ and $E(w)=\mathrm{weightFloor}\ K\ N\ m\ w$ otherwise, where $\mathrm{weightFloor}$ is the sum of $\lfloor 2m\,\mathrm{ord}_w\bar\jmath/3\rfloor$ at the zeros of $\bar\jmath$, of $\lfloor m\,\mathrm{ord}_w(\bar\jmath-1728)/2\rfloor$ at the zeros of $\bar\jmath-1728$, and of $m\,\mathrm{ord}_w\bar\jmath$ where $\mathrm{ord}_w\bar\jmath<0$ (each term $0$ otherwise). Then for $G\in F$ the following are equivalent: $G$ lies in the Riemann–Roch space of $E$, that is $w$-adic valuation of $G$ is at most $\exp(E(w))$ for every place $w$ (equivalently $\mathrm{ord}_w G\ge -E(w)$ for all $w$); and $G$, viewed as a Laurent series, satisfies $\mathrm{IsModPCuspFormFn}\ K\ m$, namely $G^6\bar\jmath^{4m}(\bar\jmath-1728)^{3m}$ is integral over $K[\bar\jmath]$ and there is some $M\in\mathbb N$ with $G^{2M}\bar\jmath^{mM+1}(\bar\jmath-1728)^{mM}$ integral over $K[\bar\jmath^{-1}]$.
--
--   This is the cuspidal half of the dictionary between the floor-divisor description of weight-$2m$ modular functions in characteristic $p$ and the description by integrality of $G^6\bar\jmath^{4m}(\bar\jmath-1728)^{3m}$ and of the twisted powers at the cusps: the extra $-1$ at each pole of $\bar\jmath$ encodes strict vanishing at the cusps. It is used to identify spaces of mod $p$ cusp forms with Riemann–Roch spaces, in the comparison of cusp-form dimensions and in the Serre-duality identification of the relevant differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub.lean

import Mathlib
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.mem_riemannRochSpace_iff_isModPCuspFormFn_of_forall_eq_weightFloor_sub
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] (m : ℕ) (hm : 1 ≤ m)
    (E : Divisor K ↥(modularFunctionFieldC K N))
    (hE : ∀ w : Place K ↥(modularFunctionFieldC K N),
      E w = ModularCurve.weightFloor K N m w - (if w.ord (jGeomGen K N) < 0 then 1 else 0))
    (G : ↥(modularFunctionFieldC K N)) :
    G ∈ AlgebraicCurve.riemannRochSpace E ↔ ModularCurve.IsModPCuspFormFn K m (G : LaurentSeries K) := by sorry
