-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_gram_trace_smul_map_volume_eq_two_pow_nrComplexPlaces_smul_volume
-- name    : NumberField.mixedEmbedding.gram_trace_smul_map_volume_eq_two_pow_nrComplexPlaces_smul_volume
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/3d0eeab2-8369-56ab-8db9-2d8f3e7a16b9
-- title:
--   Gram measure of the trace form on K_∞ equals 2^{r₂} times Lebesgue measure
-- statement:
--   Let $K$ be a number field and let $\mathrm{mixedSpace}\,K$ be its mixed space, the real algebra $\prod_{v\ \mathrm{real}}\mathbb{R}\times\prod_{v\ \mathrm{complex}}\mathbb{C}$ attached to the archimedean places of $K$, equipped with its product Lebesgue measure `volume` (on each complex factor, the Lebesgue measure of $\mathbb{R}^2$). Let $m$ be a natural number and let $b : \mathrm{Fin}\,m \to \mathrm{mixedSpace}\,K$ be a family of vectors that is linearly independent over $\mathbb{R}$ and whose $\mathbb{R}$-span is all of $\mathrm{mixedSpace}\,K$, i.e. an $\mathbb{R}$-basis indexed by $\mathrm{Fin}\,m$. Form the Gram matrix $\bigl(\operatorname{Tr}_{\mathrm{mixedSpace}\,K/\mathbb{R}}(b_a\, b_{a'})\bigr)_{a,a'}$ of the trace form of the algebra $\mathrm{mixedSpace}\,K$ over $\mathbb{R}$ in this basis. The assertion is the equality of measures on $\mathrm{mixedSpace}\,K$ $$\sqrt{\bigl|\det\bigl(\operatorname{Tr}(b_a b_{a'})\bigr)\bigr|}\cdot \Bigl(c \mapsto \sum_a c_a\, b_a\Bigr)_{*}\mathrm{Leb}_{\mathbb{R}^m} \;=\; 2^{r_2}\cdot \mathrm{Leb}_{\mathrm{mixedSpace}\,K},$$ where the scalar on the left is taken as an element of $[0,\infty]$ via `ENNReal.ofReal`, the pushforward is of Lebesgue measure on $\mathrm{Fin}\,m \to \mathbb{R}$ along the coordinate map of $b$, and $r_2 =$ `nrComplexPlaces K` is the number of complex infinite places of $K$.
--
--   This identifies the self-dual (Gram-normalised) additive Haar measure of the archimedean algebra $K_\infty$ of a number field, computed from the trace form in an arbitrary real basis, with $2^{r_2}$ times the standard product Lebesgue measure; the scaling factor is basis-independent by [`MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq`](thm.html#MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq), which the proof cites. It feeds the computation of integrals over the infinite adeles in the treatment of automorphic forms, being used in [`AutomorphicForm.lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing`](thm.html#AutomorphicForm.lintegral_mul_apply_col_det_eq_mul_lintegral_setLIntegral_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_gram_trace_smul_map_volume_eq_two_pow_nrComplexPlaces_smul_volume.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

open scoped Classical in

theorem NumberField.mixedEmbedding.gram_trace_smul_map_volume_eq_two_pow_nrComplexPlaces_smul_volume
    (K : Type) [Field K] [NumberField K]
    (m : ℕ) (b : Fin m → mixedEmbedding.mixedSpace K) (hb : LinearIndependent ℝ b)
    (hbsp : Submodule.span ℝ (Set.range b) = ⊤) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun a a' : Fin m =>
          Algebra.trace ℝ (mixedEmbedding.mixedSpace K) (b a * b a')).det|)) •
        Measure.map (fun c : Fin m → ℝ => ∑ a, c a • b a) volume =
      (2 : ENNReal) ^ NumberField.InfinitePlace.nrComplexPlaces K •
        (volume : Measure (mixedEmbedding.mixedSpace K)) := by sorry
