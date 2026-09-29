-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_smooth_pullback_snd_toBase_int_of_isUnit_natCast
-- name    : ModularCurve.IgusaScheme.smooth_pullback_snd_toBase_int_of_isUnit_natCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/49b24fc2-d40b-5bc5-a678-0ee5c79005a0
-- title:
--   Smoothness of the integral model after inverting N
-- statement:
--   Fix $N\ge 1$ (a natural number with `NeZero N`) and write $F =$ `modularFunctionFieldFull N` for the subfield of the Laurent series field $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the expansions $\mathrm{qExpand}_{\mathbb{Q}}\,d\,j_q$ for the nonzero divisors $d \mid N$, and $j =$ `jFull N` for the element $j_q$ of that field. Let $\pi =$ [`AlgebraicCurve.TwoChartIntegralModel.toBase ℤ F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258) be the structure morphism to $\operatorname{Spec}\mathbb{Z}$ of the two-chart integral model of $(F,j)$ over $\mathbb{Z}$, i.e. of the scheme obtained as the pushout of $\operatorname{Spec}$ of the inclusions of the $\mathbb{Z}$-subalgebras $\mathbb{Z}[j]$ and $\mathbb{Z}[j^{-1}]$ of $F$ into the middle chart algebra, $\pi$ being induced by the two structure maps $\mathbb{Z} \to \mathbb{Z}[j^{\pm 1}]$. Assume as instance hypotheses that $\pi$ is flat and locally of finite presentation. Let $R$ be a commutative ring equipped with a $\mathbb{Z}$-algebra structure and suppose the image of $N$ in $R$ is a unit. Then the second projection of the fibre product of $\pi$ with $\operatorname{Spec}$ of the structure map $\mathbb{Z} \to R$, that is the base-changed morphism $\mathcal{X}_{\mathbb{Z}} \times_{\operatorname{Spec}\mathbb{Z}} \operatorname{Spec} R \to \operatorname{Spec} R$, is smooth.
--
--   This is the statement that the two-chart integral model of the modular curve of level $N$ becomes smooth over any base in which the level is invertible, the classical smoothness of the model away from the level. It is used in the construction of the Deligne–Rapoport model package, in particular by the results on base change of sections and on the existence of two-line degenerations at non-smooth points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_smooth_pullback_snd_toBase_int_of_isUnit_natCast.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.smooth_pullback_snd_toBase_int_of_isUnit_natCast
    (N : ℕ) [NeZero N] (R : Type) [CommRing R] [Algebra ℤ R] (hN : IsUnit ((N : ℕ) : R))
    [Flat (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))]
    [LocallyOfFinitePresentation
      (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))] :
    Smooth
      (pullback.snd
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) := by sorry
