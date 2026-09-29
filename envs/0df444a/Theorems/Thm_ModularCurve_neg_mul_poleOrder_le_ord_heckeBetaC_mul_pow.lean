-- Prove2me | Theorems.Thm_ModularCurve_neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow
-- name    : ModularCurve.neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/f065dbd4-e8e3-5491-a6a7-1b0973cfc7fd
-- title:
--   Floor bound for β(d)h^m along a supersingular fibre
-- statement:
--   Fix a prime $p \ge 5$ and an algebraically closed field $K$ of characteristic $p$, an integer $N \ge 1$ with $N \ne 0$ in $K$, and a prime $\ell$ with $\ell \nmid N$ and $\ell \ne p$. Write $F =$ `modularFunctionFieldC K N`, the subfield of $K((q))$ generated over $K$ by `jqModC K` and `jqNModC K N`, and $R =$ `charLDegeneracyRoof K N ℓ`, generated over $K$ by `jqModC K`, `jqNModC K N`, `jqNModC K ℓ` and `jqNModC K (N*ℓ)`; let $\alpha =$ `heckeAlphaC K N ℓ` be the inclusion $F \hookrightarrow R$ and $\beta =$ `heckeBetaC K N ℓ` the other degeneracy embedding, both assumed integral. Let $m \ge 1$, let $h \in R$ and $d \in F$ be nonzero, and assume $\operatorname{ord}_z d \ge -(\mathrm{weightDivisor}\ K\ N\ m)(z)$ at every place $z$ of $F$ lying in `ssPlaces p N K` (the places satisfying `IsSupersingularPlace p N K`). Let $x$ be an element of `SSIndex p N K hp5 (2*m)`, i.e. a place $x_1$ of $F$ in `ssPlaces p N K` with $u(x_1) =$ `placeWidth N x₁` dividing $m$ (together with the numerical conditions $2 \le 2m$, $2 \mid 2m$, $5 \le p$). Let $S$ be a finite set of places of $R$ consisting exactly of the places $y$ with $y|_\alpha = x_1$, where $y|_\varphi$ denotes `Place.restrictAlong` of $y$ along $\varphi$; write $e_\varphi(y)$ for `Place.ramificationIndexAlong` and $r(w) =$ `placeRamificationJ N w`, the non-negative part of $\operatorname{ord}_w$ of `jGeomGen K N` minus its value at $w$. Assume for every $y \in S$: (H) $\operatorname{ord}_y h = e_\beta(y) r(y|_\beta) - e_\alpha(y) r(x_1)$; (W) $e_\alpha(y) u(y|_\beta) = e_\beta(y) u(x_1)$; and (S) $y|_\beta \in$ `ssPlaces p N K`. Then for every $y \in S$, $$\operatorname{ord}_y\bigl(\beta(d) h^m\bigr) \ge -e_\alpha(y)\, a(x),$$ where $a(x) =$ `poleOrder p N K hp5 (2*m) x` is the integer quotient $m\,(\mathrm{jWidth}(x_1(\mathrm{jGeomGen}\ K\ N)) - 1)/u(x_1)$.
--
--   This is the non-strict (floors-only) order estimate at the places of the degeneracy roof above a supersingular index place: assuming only that $d$ satisfies the weight-$2m$ floors at the supersingular places, the product $\beta(d)h^m$ has at worst the pole order $e_\alpha(y)a(x)$ permitted by the index datum. It feeds the additivity and scaling properties of the supersingular Hecke functional ([`ModularCurve.SSHeckeV2.ssHeckeFun_add`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_add), [`ModularCurve.SSHeckeV2.ssHeckeFun_smul`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_smul) and [`ModularCurve.SSHeckeV2.ssHeckeFun_bMul_eq_smul_bMul_ssHeckeFun`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_bMul_eq_smul_bMul_ssHeckeFun)), where the bound is combined over the fibre $S$ to control the trace from $R$ to $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_ModularCurve_SSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.neg_mul_poleOrder_le_ord_heckeBetaC_mul_pow
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (m : ℕ) (hm : 1 ≤ m) (h : ↥(charLDegeneracyRoof K N ℓ)) (hh0 : h ≠ 0)
    (d : ↥(modularFunctionFieldC K N)) (hd0 : d ≠ 0)
    (hF : ∀ z : Place K ↥(modularFunctionFieldC K N), z ∈ ssPlaces p N K →
      -(ModularCurve.weightDivisor K N m z) ≤ z.ord d)
    (x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)))
    (S : Finset (Place K ↥(charLDegeneracyRoof K N ℓ)))
    (hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ S ↔ y.restrictAlong (heckeAlphaC K N ℓ) hα = x.1)
    (hH : ∀ y ∈ S,
      y.ord h = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ)
                  * (placeRamificationJ N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
              - (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeRamificationJ N x.1 : ℤ))
    (hW : ∀ y ∈ S,
      (Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * (placeWidth N (y.restrictAlong (heckeBetaC K N ℓ) hβ) : ℤ)
        = (Place.ramificationIndexAlong (heckeBetaC K N ℓ) y : ℤ) * (placeWidth N x.1 : ℤ))
    (hS : ∀ y ∈ S, y.restrictAlong (heckeBetaC K N ℓ) hβ ∈ ssPlaces p N K) :
    ∀ y ∈ S, -((Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ)
        * ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x) ≤ y.ord (heckeBetaC K N ℓ d * h ^ m) := by sorry
