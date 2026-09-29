-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_setLIntegral_setOf_forall_normAtPlace_mem_Icc_one_exp_inv_norm_eq_two_pow_mul_two_pi_pow
-- name    : NumberField.mixedEmbedding.setLIntegral_setOf_forall_normAtPlace_mem_Icc_one_exp_inv_norm_eq_two_pow_mul_two_pi_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/7b552fea-cc07-5ac5-ba4f-42de92cb4111
-- title:
--   Mass of the archimedean unit shell for dx/N(x)
-- statement:
--   Let $K$ be a number field. Work in the mixed space $K_\infty = \prod_{w\ \text{real}}\mathbb{R}\times\prod_{w\ \text{complex}}\mathbb{C}$ attached to $K$, equipped with its canonical additive Haar (product Lebesgue) measure `volume`, where the complex factors carry the Lebesgue measure of $\mathbb{R}^2$. For an infinite place $w$ of $K$ and $x\in K_\infty$, let `normAtPlace w x` be the absolute value of the $w$-component of $x$, and let `mixedEmbedding.norm x` $=\prod_w (\mathrm{normAtPlace}\,w\,x)^{\mathrm{mult}(w)}$ be the associated real norm, the exponent $\mathrm{mult}(w)$ being $1$ at a real place and $2$ at a complex place. The assertion is an identity in $[0,\infty]$ between lower Lebesgue integrals: the integral over the shell $\{x\in K_\infty : 1\le \mathrm{normAtPlace}\,w\,x\le e \text{ for every infinite place } w\}$ of the function $x\mapsto (\mathrm{ofReal}(\mathrm{norm}\,x))^{-1}$, the inverse being taken in $[0,\infty]$, equals $2^{r_1}\cdot \mathrm{ofReal}\big((2\pi)^{r_2}\big)$, where $r_1$ = `nrRealPlaces K` and $r_2$ = `nrComplexPlaces K` are the numbers of real and of complex places of $K$.
--
--   This is the classical computation of the volume of the archimedean unit shell with respect to the multiplicative measure $dx/N(x)$, which on $K_\infty^\times$ is a Haar measure of $(\mathbb{R}^\times)^{r_1}\times(\mathbb{C}^\times)^{r_2}$: by Tonelli the integral factors into $\int_{1\le|t|\le e} dt/|t| = 2$ at each real place and $\int_{1\le|z|\le e} dA/|z|^2 = 2\pi$ at each complex place. It feeds the normalisation of an archimedean integral in the adelic theory of automorphic forms, being used in [`AutomorphicForm.setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing`](thm.html#AutomorphicForm.setLIntegral_ofReal_norm_det_eq_mul_two_pow_mul_two_pi_pow_of_map_coe_eq_smul_withDensity_gram_infiniteAdeleRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_setLIntegral_setOf_forall_normAtPlace_mem_Icc_one_exp_inv_norm_eq_two_pow_mul_two_pi_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ENNReal

open scoped Classical in

theorem NumberField.mixedEmbedding.setLIntegral_setOf_forall_normAtPlace_mem_Icc_one_exp_inv_norm_eq_two_pow_mul_two_pi_pow
    (K : Type) [Field K] [NumberField K] :
    ∫⁻ x in {x : mixedSpace K | ∀ w : InfinitePlace K, normAtPlace w x ∈ Set.Icc 1 (Real.exp 1)},
        (ENNReal.ofReal (mixedEmbedding.norm x))⁻¹ ∂volume =
      2 ^ nrRealPlaces K * ENNReal.ofReal ((2 * Real.pi) ^ nrComplexPlaces K) := by sorry
