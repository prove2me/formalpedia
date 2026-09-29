-- Prove2me | Theorems.Thm_ModularCurve_ordDifferential_D_jGeomGen_sub_weightFloor_eq
-- name    : ModularCurve.ordDifferential_D_jGeomGen_sub_weightFloor_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/7a2a0f36-3a1c-59eb-ac6a-edff420a1626
-- title:
--   Placewise identity for ord_w(d̄ j) and weight floors
-- statement:
--   Fix a prime $p\ge 5$, a level $N\ge 1$ with $p\nmid N$, and an algebraically closed field $K$ of characteristic $p$; put $F=\operatorname{modularFunctionFieldC} K N=K(j(q),j(q^N))\subseteq K((q))$, generated inside the Laurent series over $K$ by the mod-$p$ $j$-series `jqModC K` and its $N$-th analogue, and write $\bar j=$ `jGeomGen K N` for the element of $F$ given by `jqModC K`. Assume that at every place $w$ of $F/K$ (a proper valuation subring of $F$ containing $K$ whose ring is a principal ideal ring) the differential $D(\pi_w)$ of a uniformiser spans $\Omega_{F/K}$ over $F$, and that $\Omega_{F/K}\ne 0$. Let $m,m'\in\mathbb{N}$ with $m+m'=(p+1)/2$, and let $h\in F$ have $q$-expansion $(\theta\,\bar j)^{-(p-1)/2}$, where $\theta f=q\,df/dq$ is the operator `thetaL`. For $ω\in\Omega_{F/K}$ let $\operatorname{ord}^{\mathrm{diff}}_w(ω)$ denote $\operatorname{ord}_w$ of the coefficient $f$ in $ω=f\cdot D(\pi_w)$, and set
--   $$W_m(w)=\Big[\tfrac{2m\,\operatorname{ord}_w\bar j}{3}\Big]_{\operatorname{ord}_w\bar j>0}+\Big[\tfrac{m\,\operatorname{ord}_w(\bar j-1728)}{2}\Big]_{\operatorname{ord}_w(\bar j-1728)>0}+\big[m\,\operatorname{ord}_w\bar j\big]_{\operatorname{ord}_w\bar j<0},$$
--   the function `weightFloor K N m`, each bracket being the integer quotient when the indicated inequality holds and $0$ otherwise. Then for every place $w$ of $F/K$ three implications hold. First, if $w$ is a supersingular place for $p$ and the width $\operatorname{placeWidth} N w=\mathrm{jWidth}(w(\bar j))/\operatorname{placeRamificationJ} N w$ divides $m$, then $\operatorname{ord}^{\mathrm{diff}}_w(D\bar j)-W_m(w)+1=W_{m'}(w)+\operatorname{ord}_w h$. Second, if $w$ is affine, in the sense that both $\bar j$ and $j(q^N)$ lie in the valuation subring of $w$, and $w$ fails to satisfy the previous pair of conditions, then $\operatorname{ord}^{\mathrm{diff}}_w(D\bar j)-W_m(w)=W_{m'}(w)+\operatorname{ord}_w h$. Third, if $\operatorname{ord}_w\bar j<0$ and the image in $K$ of $|\operatorname{ord}_w\bar j|$ is non-zero, then $\operatorname{ord}^{\mathrm{diff}}_w(D\bar j)-W_m(w)=W_{m'}(w)-1+\operatorname{ord}_w h$.
--
--   This is the placewise form of the divisor identity $K_{\mathrm{can}}-(D_{2m}-SS^*_m)=D^{\mathrm{cusp}}_{2m'}+\operatorname{div}(h)$, with $2m+2m'=p+1$, which is the Kodaira–Spencer and Hasse-invariant bookkeeping underlying the Katz–Edixhoven comparison between differentials bounded by the supersingular-corrected weight-$2m$ floor and mod-$p$ forms of weight $2m'$. It is used in the proof that $ω=f\,d\bar j\mapsto f\,h$ identifies the relevant space of differentials with the space of weight-$2m'$ mod-$p$ cusp functions, namely by [`ModularCurve.weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn`](thm.html#ModularCurve.weilOfKaehler_smul_D_jGeomGen_mem_omegaSpace_iff_isModPCuspFormFn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ordDifferential_D_jGeomGen_sub_weightFloor_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.ordDifferential_D_jGeomGen_sub_weightFloor_eq
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates]
    [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
    (m m' : ℕ) (hmm' : m + m' = (p + 1) / 2)
    (h : ↥(modularFunctionFieldC K N)) (hh : (h : LaurentSeries K) = thetaL K (jqModC K) ^ (-(((p : ℤ) - 1) / 2)))
    (w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) :
    (w ∈ ssPlaces p N K → ((placeWidth N w : ℤ) ∣ (m : ℤ)) →
      w.ordDifferential (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) - weightFloor K N m w + 1
        = weightFloor K N m' w + w.ord h) ∧
    (IsAffineGeomPlace K N w → ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) →
      w.ordDifferential (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) - weightFloor K N m w
        = weightFloor K N m' w + w.ord h) ∧
    (w.ord (jGeomGen K N) < 0 → (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0 →
      w.ordDifferential (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)) - weightFloor K N m w
        = weightFloor K N m' w - 1 + w.ord h) := by sorry
