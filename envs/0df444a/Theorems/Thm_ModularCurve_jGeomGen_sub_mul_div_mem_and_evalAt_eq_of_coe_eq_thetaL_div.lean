-- Prove2me | Theorems.Thm_ModularCurve_jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div
-- name    : ModularCurve.jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/c6f2ca41-2ab4-52a1-be16-7171993f766d
-- title:
--   Value of (jmath̄-j₀) θ f/(thetajmath̄ f) at an affine place
-- statement:
--   Let $p\ge 5$ be a prime, let $N\ge 1$ be an integer with $p\nmid N$, and let $K$ be an algebraically closed field of characteristic $p$. Write $F=$ `modularFunctionFieldC K N` for the intermediate field of $K((q))=$ `LaurentSeries K` generated over $K$ by the two Laurent series `jqModC K` (the $q$-expansion $q^{-1}E_4^3\eta^{-24}$-type series $\bar\jmath$) and `jqNModC K N` (its $q\mapsto q^N$ substitution $\bar\jmath_N$). Let $x$ be a place of $F$ over $K$, that is a valuation subring of $F$ containing $\operatorname{im}(K\to F)$, not equal to $F$ and a principal ideal ring; assume $x$ is rational, i.e. $K$ surjects onto its residue field, and that $x$ is affine in the sense that both `jGeomGen K N` $=\bar\jmath$ and `jNGeomGen K N` $=\bar\jmath_N$ lie in the valuation subring. Let $f,g\in F$ with $f\neq 0$, and suppose the $q$-expansion of $g$ is $\theta f/\theta\bar\jmath$, where $\theta=$ `thetaL K` is the $K$-linear operator $h\mapsto q\,h'$ on $K((q))$. Put $j_0=x(\bar\jmath)\in K$, the value `x.evalAt (jGeomGen K N)` obtained from the residue map and the inverse of $K\to$ `x.ResidueField`. Then $(\bar\jmath-j_0)g/f$ lies in the valuation subring of $x$, and its value at $x$ equals $\operatorname{ord}_x(f)$ divided by `placeRamificationJ N x`, both images in $K$ of integers, the latter being $\operatorname{ord}_x(\bar\jmath-j_0)$ truncated to $\mathbb N$; here $\operatorname{ord}_x$ is minus the logarithm of the adic valuation attached to $x$.
--
--   This is the residue formula for the logarithmic derivative along the $j$-line: the regular function $(\bar\jmath-j_0)\,(df/d\bar\jmath)/f$ computes, at an affine rational place of the modular function field in characteristic $p\ge5$, the order of vanishing of $f$ divided by the ramification index of that place over the $j$-line. It is used in the analysis of supersingular places, in particular by [`ModularCurve.stackOrd_qP_mul_thetaL_jqModC_zpow_eq_zero_of_mem_ssPlaces`](thm.html#ModularCurve.stackOrd_qP_mul_thetaL_jqModC_zpow_eq_zero_of_mem_ssPlaces).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (x : Place K (modularFunctionFieldC K N)) (hxr : x.IsRational) (hx : IsAffineGeomPlace K N x)
    (f g : ↥(modularFunctionFieldC K N)) (hf : f ≠ 0)
    (hg : (g : LaurentSeries K) = thetaL K (f : LaurentSeries K) / thetaL K (jqModC K)) :
    (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) (x.evalAt (jGeomGen K N))) * g / f
        ∈ x.toValuationSubring ∧
      x.evalAt ((jGeomGen K N - algebraMap K (modularFunctionFieldC K N) (x.evalAt (jGeomGen K N))) * g / f)
        = ((x.ord f : ℤ) : K) / ((placeRamificationJ N x : ℕ) : K) := by sorry
