-- Prove2me | Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
-- name    : NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/069904de-8202-50fb-ae37-8fbe3dfb2be9
-- title:
--   Convergence, holomorphy and non-vanishing of degree-one Euler products
-- statement:
--   Let $M$ be a number field, with ring of integers $\mathcal{O}_M$, and let $S$ be a finite set of height-one primes of $\mathcal{O}_M$ (non-zero prime ideals, in the `HeightOneSpectrum` formulation). Let $z$ assign to every height-one prime $v \notin S$ a complex number $z_v$, subject to the hypothesis $\lVert z_v\rVert \le 1$ for all such $v$. Writing $Nv =$ `Ideal.absNorm` of the ideal underlying $v$, regarded as a natural number and then as a complex number, and using the complex power $Nv^{-s}$, the conclusion is a threefold assertion about the factors $(1 - z_v\, Nv^{-s})^{-1}$ indexed by the subtype of primes not in $S$: first, for every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1$ the family of these factors is multipliable, i.e. its finite partial products converge along the filter of finite subsets of the index set; second, the function sending $s$ to the unconditional product $\prod'_{v \notin S} (1 - z_v\, Nv^{-s})^{-1}$ is differentiable on the half-plane $\{s : \operatorname{Re} s > 1\}$; third, for every $s$ with $\operatorname{Re} s > 1$ that product is non-zero.
--
--   This is the elementary analytic input on Euler products of degree one with bounded coefficients: absolute (unconditional) convergence, holomorphy and non-vanishing in the half-plane $\operatorname{Re} s > 1$, as for Hecke $L$-series attached to unramified characters. It is used throughout the analytic part of the development, in particular in the Rankin–Selberg constructions, whenever an Euler product away from a finite set of primes must be known to define a non-vanishing holomorphic function to the right of the line $\operatorname{Re} s = 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
    (M : Type) [Field M] [NumberField M] (S : Finset (HeightOneSpectrum (𝓞 M)))
    (z : {v : HeightOneSpectrum (𝓞 M) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) :
    (∀ s : ℂ, 1 < s.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S} =>
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) ∧
      DifferentiableOn ℂ
        (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S},
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
        {s : ℂ | 1 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S},
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ≠ 0 := by sorry
