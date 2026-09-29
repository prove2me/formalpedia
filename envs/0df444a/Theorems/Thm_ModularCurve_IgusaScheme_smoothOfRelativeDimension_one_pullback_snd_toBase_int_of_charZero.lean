-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charZero
-- name    : ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/6e35db3c-7787-53f5-bb09-3e1b641f7214
-- title:
--   Smoothness of characteristic-zero fibres of the integral model
-- statement:
--   Let $N$ be a nonzero natural number and let $K$ be a field of characteristic $0$. Write $F =$ `modularFunctionFieldFull N` for the intermediate field of the Laurent series field $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set of $q$-expansions `qExpand ℚ d jq` for the nonzero divisors $d \mid N$, and let `jFull N` $\in F$ be the element given by the $q$-expansion $j_q$ of the $j$-function. The two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel ℤ F (jFull N)`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two morphisms `fFin` and `fInf` of affine schemes induced by the inclusions of the subalgebras `chartAlg ℤ F {jFull N}` and `chartAlg ℤ F {(jFull N)⁻¹}` of $F$ into the middle chart, and `toBase` is the morphism from this pushout to $\operatorname{Spec} \mathbb{Z}$ determined by the two structure morphisms $\mathbb{Z} \to$ `chartAlg ℤ F {jFull N}` and $\mathbb{Z} \to$ `chartAlg ℤ F {(jFull N)⁻¹}`. The assertion is that the second projection of the fibre product of `toBase` with $\operatorname{Spec}$ of the structure map $\mathbb{Z} \to K$, that is the morphism $\mathcal{X}_{\mathbb{Z}} \times_{\operatorname{Spec}\mathbb{Z}} \operatorname{Spec} K \to \operatorname{Spec} K$, is smooth of relative dimension $1$.
--
--   This is the statement that every characteristic-zero fibre of the two-chart integral model attached to the full modular function field of level $N$ is a smooth curve, in the tradition of Igusa's Kroneckerian model of $X_0(N)$ over $\mathbb{Z}$. It is used in the geometric input to the level-lowering and modularity arguments, in particular by the results describing the rational fibre of the model and of the Igusa scheme (integrality, local Noetherianness and the stalks, and smoothness together with geometric integrality of the rational fibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charZero.lean

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

theorem ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_snd_toBase_int_of_charZero
    (N : ℕ) [NeZero N] (K : Type) [Field K] [CharZero K] :
    SmoothOfRelativeDimension 1
      (pullback.snd
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) := by sorry
