-- Prove2me | Theorems.Thm_ModularCurve_diffQExp_map_eq_coeffMap_diffQExp
-- name    : ModularCurve.diffQExp_map_eq_coeffMap_diffQExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/f1aff100-c157-5cb4-a882-903d22f2f16f
-- title:
--   q-expansion of Kähler differentials commutes with coefficient extension
-- statement:
--   Let $k \subseteq K$ be fields with $K$ a $k$-algebra, and let $\Gamma$ be a subgroup of $\mathrm{SL}(2,\mathbb{Z})$. Write $F_k =$ [`ModularCurve.qExpFunctionFieldC k Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $k((q))$ generated over $k$ by the ratios $\mathrm{intSeriesC}\,k\,p_f / \mathrm{intSeriesC}\,k\,p_g$ of the integral $q$-expansions $p_f, p_g$ of modular forms of level $\Gamma$ (with nonzero denominator), and similarly $F_K \subseteq K((q))$. Assume given algebra structures making $F_K$ an algebra over $F_k$ and over $k$, with the scalar-tower and scalar-commutation compatibilities for $k \to K \to F_K$ and $k \to F_k \to F_K$, and assume the hypothesis $h\iota$ that this $F_k$-algebra structure is the coefficientwise one: for every $x \in F_k$, the image of $x$ in $F_K \subseteq K((q))$ equals [`ModularCurve.coeffMap (algebraMap k K)`](def/ModularCurve_LaurentCoeff.html#L16) applied to $x \in k((q))$, where `coeffMap` applies a ring homomorphism to each Laurent coefficient. Then for every $\omega \in \Omega_{F_k/k}$, the $F_K$-linear map [`ModularCurve.diffQExp`](def/ModularCurve_HeckeDifferential.html#L128) attached to $F_K$ — the lift to $\Omega_{F_K/K}$ of the Euler derivation $q\,d/dq$ on $K((q))$ restricted along $F_K$ — sends the base-changed differential `KaehlerDifferential.map k K F_k F_K ω` to the coefficientwise image under $k \to K$ of `diffQExp` $F_k$ $\omega$.
--
--   This is the statement that the $q$-expansion map on Kähler differentials of the $q$-expansion function field of level $\Gamma$ is compatible with extension of the coefficient field, the differential-form analogue of the compatibility of $q$-expansions with base change. It is used in the verification that, away from the supersingular $q$-expansion places, the $q$-expansion of a differential attached to a cusp form with integral $q$-expansion is regular and is given by the integral series, where one passes from a base field to an extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diffQExp_map_eq_coeffMap_diffQExp.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.diffQExp_map_eq_coeffMap_diffQExp
    (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K] (Γ : Subgroup SL(2, ℤ))
    [Algebra ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)] [Algebra k ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    [IsScalarTower k K ↥(ModularCurve.qExpFunctionFieldC K Γ)] [IsScalarTower k ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    [SMulCommClass K ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    (hι : ∀ x : ↥(ModularCurve.qExpFunctionFieldC k Γ),
      ((algebraMap ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) x : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) =
        ModularCurve.coeffMap (algebraMap k K) (x : LaurentSeries k))
    (ω : Ω[↥(ModularCurve.qExpFunctionFieldC k Γ)⁄k]) :
    ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K Γ) (KaehlerDifferential.map k K ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) ω) =
      ModularCurve.coeffMap (algebraMap k K) (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC k Γ) ω) := by sorry
