-- Prove2me | Theorems.Thm_ModularCurve_neg_mul_add_one_le_ord_pow_mul_heckeBetaC_mul_pow_sub_of_mem_ssPlaces
-- name    : ModularCurve.neg_mul_add_one_le_ord_pow_mul_heckeBetaC_mul_pow_sub_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/d99e7fd1-db7f-5e1e-9bbd-63bb705dd786
-- title:
--   Supersingular order bound for the Hecke difference on the roof
-- statement:
--   Let $p\ge 5$ be prime and let $K$ be an algebraically closed field of characteristic $p$ with decidable equality; let $N\ge 1$ and $\ell$ prime with $(N:K)\neq 0$, $\ell\nmid N$ and $\ell\neq p$. Write $F=$ `modularFunctionFieldC K N`, the subfield of $K((q))$ generated over $K$ by `jqModC K` and `jqNModC K N`, and $R=$ `charLDegeneracyRoof K N ℓ`, generated over $K$ by `jqModC K`, `jqNModC K N`, `jqNModC K ℓ` and `jqNModC K (N*ℓ)`; assume the inclusion $\alpha=$ `heckeAlphaC K N ℓ` $: F\to R$ is integral. Let $b\in F$ have $q$-expansion $q_P\cdot(\theta\bar\jmath)^{-\lfloor (p+1)/2\rfloor}$, where $\theta f=q\,df/dq$ and $\bar\jmath=$ `jqModC K`, and let $h\in R$ satisfy $h\cdot\theta\bar\jmath=\ell\cdot(\theta\bar\jmath)(q^{\ell})$, the substitution $q\mapsto q^{\ell}$ being `qExpand K ℓ`. Let $x$ be a place of $F$ over $K$ lying in `ssPlaces p N K`, and let $S$ be a finset of places of $R$ containing exactly those $y$ whose restriction to $F$ along $\alpha$ is $x$. Then for every $y\in S$,
--   $$\operatorname{ord}_y\!\left(\ell^{(p+1)/2}\,\beta(b)\,h^{(p+1)/2}-\ell\,\alpha(b)\right)\;\ge\;-e_\alpha(y)\cdot\frac{\tfrac{p+1}{2}\,(W(x)-1)}{u(x)}+1,$$
--   where $\beta=$ `heckeBetaC K N ℓ`, $e_\alpha(y)$ is the ramification index of $y$ along $\alpha$, $W(x)=$ `jWidth` of the residue value of `jGeomGen K N` at $x$ (equal to $3$, $2$ or $1$ according as this value is $0$, $1728$ or otherwise), $u(x)=$ `placeWidth N x`, and the quotient is integer division in $\mathbb{Z}$.
--
--   This is the statement that the weight-$(p+1)$ function attached to $\ell E_2(\ell\tau)-E_2(\tau)$, written on the $\ell$-degeneracy roof as $\ell^{(p+1)/2}\beta(b)h^{(p+1)/2}-\ell\,\alpha(b)$, exceeds the supersingular pole bound of the weight-$(p+1)$ floor by one at every place above a supersingular place. It feeds the semilinearity of the Hecke operator on the supersingular module, being used in [`ModularCurve.SSHeckeV2.ssHeckeFun_bMul_eq_smul_bMul_ssHeckeFun`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_bMul_eq_smul_bMul_ssHeckeFun).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_neg_mul_add_one_le_ord_pow_mul_heckeBetaC_mul_pow_sub_of_mem_ssPlaces.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_SwdAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.neg_mul_add_one_le_ord_pow_mul_heckeBetaC_mul_pow_sub_of_mem_ssPlaces
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral)
    (b : ↥(modularFunctionFieldC K N))
    (hb : (b : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)))
    (h : ↥(charLDegeneracyRoof K N ℓ))
    (hh : ((h : ↥(charLDegeneracyRoof K N ℓ)) : LaurentSeries K) * thetaL K (jqModC K) = (ℓ : K) • qExpand K ℓ (thetaL K (jqModC K)))
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x ∈ ssPlaces p N K)
    (S : Finset (Place K ↥(charLDegeneracyRoof K N ℓ)))
    (hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ S ↔ y.restrictAlong (heckeAlphaC K N ℓ) hα = x) :
    ∀ y ∈ S,
      -((Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ)
          * ((((p : ℤ) + 1) / 2) * ((jWidth (x.evalAt (jGeomGen K N)) : ℤ) - 1) / (placeWidth N x : ℤ))) + 1
        ≤ y.ord (algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ ((p + 1) / 2)) * heckeBetaC K N ℓ b * h ^ ((p + 1) / 2)
                  - algebraMap K ↥(charLDegeneracyRoof K N ℓ) (ℓ : K) * heckeAlphaC K N ℓ b) := by sorry
