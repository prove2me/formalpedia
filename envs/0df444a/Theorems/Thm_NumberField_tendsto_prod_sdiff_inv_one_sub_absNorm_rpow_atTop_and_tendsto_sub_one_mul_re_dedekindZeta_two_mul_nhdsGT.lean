-- Prove2me | Theorems.Thm_NumberField_tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT
-- name    : NumberField.tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/cdd1be93-d304-581d-a273-d242cc597017
-- title:
--   Euler product and residue of ζ_K(2s)ζ_K(2s-1) in [0,∞]
-- statement:
--   Let $K$ be a number field and let $S$ be a finite set of finite places of $K$, i.e. a finite subset of the height-one spectrum of the ring of integers $\mathcal{O}_K$; for such a place $v$ write $q_v$ for the absolute norm of the prime ideal $v$. The theorem is the conjunction of three assertions. First, for every real $s>1$ the real part of $\zeta_K(2s)\,\zeta_K(2s-1)$ is positive. Second, for every real $s>1$ the net of finite products $\prod_{v\in T\setminus S}(1-q_v^{-2s})^{-1}(1-q_v^{1-2s})^{-1}$, computed in $[0,\infty]$ with $\mathbb{R}_{\ge 0}^{\infty}$-valued real powers and inverses, indexed by the finite sets $T$ of finite places ordered by inclusion, converges along the at-top filter to $\mathrm{ofReal}\big(\operatorname{Re}(\zeta_K(2s)\zeta_K(2s-1))\big)\cdot\prod_{v\in S}(1-q_v^{-2s})(1-q_v^{1-2s})$. Third, as $s\to 1^{+}$ through real values (the limit along the neighbourhood filter of $1$ within $(1,\infty)$), the quantity $\mathrm{ofReal}(s-1)$ times that last expression converges in $[0,\infty]$ to $\mathrm{ofReal}\big(\operatorname{Re}(\zeta_K(2))\cdot(\rho_K/2)\big)\cdot\prod_{v\in S}(1-q_v^{-2})(1-q_v^{-1})$, where $\rho_K$ is the residue of $\zeta_K$ at $s=1$ as given by `NumberField.dedekindZeta_residue`.
--
--   This is the Euler product for $\zeta_K(2s)\zeta_K(2s-1)$ with the factors at a finite bad set $S$ removed, together with the behaviour of the resulting product as $s\to 1^{+}$, packaged with values in $[0,\infty]$ so that it can be fed directly into a computation of an integral over a restricted product. It is obtained from the complex-valued Euler product and residue statement [`NumberField.hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT`](thm.html#NumberField.hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT), and is used in the evaluation of the zeta integral of the unit group of a quaternion algebra, where the local factor at every place outside $S$ equals $(1-q_v^{-2s})^{-1}(1-q_v^{1-2s})^{-1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter Topology NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∀ s : ℝ, 1 < s →
      0 < (NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re) ∧
    (∀ s : ℝ, 1 < s →
      Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) =>
          ∏ v ∈ T \ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s)))⁻¹ *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s))⁻¹))
        atTop
        (𝓝 (ENNReal.ofReal
              ((NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re) *
          ∏ v ∈ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s)))))) ∧
    Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) *
        (ENNReal.ofReal
            ((NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re) *
          ∏ v ∈ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s)))))
      (𝓝[>] (1 : ℝ))
      (𝓝 (ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * (NumberField.dedekindZeta_residue K / 2)) *
          ∏ v ∈ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(1 : ℝ)))))) := by sorry
