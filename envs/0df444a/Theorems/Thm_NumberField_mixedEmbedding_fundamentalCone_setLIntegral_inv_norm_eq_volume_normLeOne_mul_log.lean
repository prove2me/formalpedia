-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log
-- name    : NumberField.mixedEmbedding.fundamentalCone.setLIntegral_inv_norm_eq_volume_normLeOne_mul_log
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/a955cdc0-b30f-5717-ba59-29e8f6ece887
-- title:
--   Norm slabs of the fundamental cone: int dV/N = vol(N≤ 1)log(b/a)
-- statement:
--   Let $K$ be a number field, viewed inside its mixed space $E_K=\prod_{v\ \mathrm{real}}\mathbb{R}\times\prod_{v\ \mathrm{complex}}\mathbb{C}$ equipped with its Lebesgue (additive Haar) measure `volume`, let $N=$ `NumberField.mixedEmbedding.norm` be the norm map on $E_K$, and let $C=$ `NumberField.mixedEmbedding.fundamentalCone K` be the fundamental cone of $K$. Let $a,b$ be real numbers with $0<a$ and $a\le b$. The assertion is the equality of extended non-negative reals
--   $$\int^{-}_{C\,\cap\,\{x\,:\,N(x)\in[a,b]\}} \mathrm{ofReal}\bigl(N(x)^{-1}\bigr)\,d\,\mathrm{volume}(x)\;=\;\mathrm{volume}\bigl(\mathrm{normLeOne}\,K\bigr)\cdot\mathrm{ofReal}\bigl(\log(b/a)\bigr),$$
--   where the left-hand side is the lower Lebesgue integral of the $[0,\infty]$-valued function $x\mapsto \mathrm{ofReal}(N(x)^{-1})$ over the part of the fundamental cone on which the norm lies in the closed interval $[a,b]$, and $\mathrm{normLeOne}\,K$ is the part of the fundamental cone on which the norm is at most $1$. In words: the mass of the measure $dV/N$ on a norm slab of the fundamental cone is the volume of the norm-at-most-one part of the cone times $\log(b/a)$.
--
--   Since $dV/N$ is, on the locus $N\neq 0$, a Haar measure for the multiplicative group $K_\infty^{\times}$, this computes the multiplicative-Haar mass of a norm slab of a fundamental domain for the units modulo torsion; combined with the evaluation of $\mathrm{vol}(\mathrm{normLeOne}\,K)$ as $2^{r_1}\pi^{r_2}R_K$ it supplies the archimedean, regulator-carrying factor in the volume computation of Tate's thesis. It is used in the computation of the measure of the norm-restricted part of a fundamental domain for the idele class group in terms of the regulator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped Classical

theorem NumberField.mixedEmbedding.fundamentalCone.setLIntegral_inv_norm_eq_volume_normLeOne_mul_log
    (K : Type) [Field K] [NumberField K] (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ x in NumberField.mixedEmbedding.fundamentalCone K ∩
        {x | NumberField.mixedEmbedding.norm x ∈ Set.Icc a b},
        ENNReal.ofReal (NumberField.mixedEmbedding.norm x)⁻¹ =
      volume (NumberField.mixedEmbedding.fundamentalCone.normLeOne K) * ENNReal.ofReal (Real.log (b / a)) := by sorry
