-- Prove2me | Theorems.Thm_ModularCurve_mem_riemannRochSpace_weightDivisor_iff_isModPFormFn
-- name    : ModularCurve.mem_riemannRochSpace_weightDivisor_iff_isModPFormFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/b6c7fd08-35a1-5d4d-9203-7100392afec7
-- title:
--   Riemann–Roch space of the weight divisor equals mod-p forms
-- statement:
--   Fix a prime $p$ with $5\le p$, an integer $N\ge 1$ with $p\nmid N$, an algebraically closed field $K$ of characteristic $p$, and $m\in\mathbb N$. Let $F=\operatorname{modularFunctionFieldC} K N$ be the intermediate field of the Laurent series field $\mathrm{LaurentSeries}\,K$ generated over $K$ by the two series $\bar\jmath=\operatorname{jqModC} K$ and its $N$-fold $q$-substitution $\operatorname{jqNModC} K N$, and let $G\in F$. The theorem asserts the equivalence of two conditions on $G$. First, $G$ lies in $\operatorname{riemannRochSpace}(\operatorname{weightDivisor} K N m)$: for every place $v$ of $F$ over $K$ (a valuation subring of $F$ containing $K$, proper, with principal ideals) one has $v.\mathrm{adicValuation}\,G\le \exp(D\,v)$, where $D=\operatorname{weightDivisor} K N m$ is the finitely supported divisor taking at each place $w$ the value $\lfloor 2m\cdot\mathrm{ord}_w(\bar\jmath)/3\rfloor$ if $\mathrm{ord}_w(\bar\jmath)>0$, plus $\lfloor m\cdot\mathrm{ord}_w(\bar\jmath-1728)/2\rfloor$ if $\mathrm{ord}_w(\bar\jmath-1728)>0$, plus $m\cdot\mathrm{ord}_w(\bar\jmath)$ if $\mathrm{ord}_w(\bar\jmath)<0$ (and is $0$ should no such divisor exist). Second, $\operatorname{IsModPFormFn} K m$ holds for $G$ viewed as a Laurent series, i.e. $G^6\bar\jmath^{4m}(\bar\jmath-1728)^{3m}$ is integral over $K[\bar\jmath]$ and $G^2\bar\jmath^{m}(\bar\jmath-1728)^{m}$ is integral over $K[\bar\jmath^{-1}]$.
--
--   This is the dictionary between the divisorial description of holomorphic weight-$2m$ modular functions in characteristic $p$ — sections of the $m$-th power of the sheaf attached to $(d\bar\jmath)^{m}$, encoded by the floor divisor at the elliptic points $\bar\jmath=0,1728$ and at the cusps — and the integrality description over $K[\bar\jmath]$ and $K[\bar\jmath^{-1}]$. It is used in the construction and analysis of Hecke operators on mod-$p$ forms in the supersingular setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_riemannRochSpace_weightDivisor_iff_isModPFormFn.lean

import Mathlib
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.mem_riemannRochSpace_weightDivisor_iff_isModPFormFn
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K]
    (m : ℕ) (G : ↥(modularFunctionFieldC K N)) :
    G ∈ riemannRochSpace (weightDivisor K N m) ↔ IsModPFormFn K m (G : LaurentSeries K) := by sorry
