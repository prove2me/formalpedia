-- Prove2me | Theorems.Thm_NumberField_tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop
-- name    : NumberField.tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/f7cbc6ff-fefe-5998-b82f-ce203b93561a
-- title:
--   Divergence at s=1⁺ of the Euler product off a finite set
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$, and let $T$ be a finite set of height-one primes of $\mathcal{O}_K$ (i.e. nonzero prime ideals, as elements of `HeightOneSpectrum (𝓞 K)`). For a real number $\sigma$ consider the unconditional product, indexed by the subtype of those height-one primes $v$ of $\mathcal{O}_K$ with $v \notin T$, of the complex numbers $\bigl(1 - (Nv)^{-\sigma}\bigr)^{-1}$, where $Nv$ denotes the absolute norm `Ideal.absNorm` of the ideal underlying $v$, viewed as a natural number and then as a complex number, and the power is the complex power with exponent $-(\sigma : \mathbb{C})$. The assertion is that the real-valued function sending $\sigma$ to the complex absolute value of this product tends to $+\infty$ (the filter `atTop` on $\mathbb{R}$) along the filter of punctured right-hand neighbourhoods of $1$, that is, as $\sigma \to 1$ with $\sigma > 1$. Note that the product is formed as a `tprod`, so no convergence hypothesis is imposed; for $\sigma > 1$, where it converges absolutely, its value is $\zeta_K(\sigma)\prod_{v \in T}\bigl(1 - (Nv)^{-\sigma}\bigr)$.
--
--   This is the divergence, as $s$ decreases to $1$ through real values, of the Euler product of the Dedekind zeta function of $K$ with the finitely many Euler factors at a prescribed finite set $T$ of primes removed; equivalently it records the pole of $\zeta_K$ at $s = 1$. It is used in the global part of the Tate-theoretic development, in [`NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar`](thm.html#NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Filter Topology

theorem NumberField.tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto
      (fun σ : ℝ => ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖)
      (𝓝[>] 1) atTop := by sorry
