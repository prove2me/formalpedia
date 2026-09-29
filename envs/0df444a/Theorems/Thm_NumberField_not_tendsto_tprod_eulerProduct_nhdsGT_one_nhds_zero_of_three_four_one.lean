-- Prove2me | Theorems.Thm_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one
-- name    : NumberField.not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/c43e8756-a72f-5800-af75-257ea1ed1454
-- title:
--   No vanishing of Euler products at σdownarrow 1
-- statement:
--   Let $K$ be a number field, $T$ a finite set of height-one primes of $\mathcal{O}_K$, and let $(a_v)$ and $(b_v)$ be families of complex numbers indexed by the primes $v$ of $\mathcal{O}_K$ with $v\notin T$. Assume that for every such $v$ either $\|a_v\|=1$ and $b_v=a_v^2$, or $a_v=0$ and $\|b_v\|\le 1$. Write $Nv=$ `Ideal.absNorm` of the ideal underlying $v$, and for a family $(c_v)$ let $E_c(s)$ denote the unconditional (`tprod`) product $\prod_{v\notin T}(1-c_v\,Nv^{-s})^{-1}$. Assume three further hypotheses: (i) there are real $C$ and $\delta>0$ with $\|\prod_{v\notin T}(1-Nv^{-\sigma})^{-1}\|\le C/(\sigma-1)$ for all real $\sigma$ with $1<\sigma<1+\delta$; (ii) there are a neighbourhood $U$ of $1$ in $\mathbb{C}$ and a function $L$ differentiable on $U$ with $L(s)=E_a(s)$ for every $s\in U$ with $\operatorname{Re}s>1$; (iii) there are real $B$ and $\delta>0$ with $\|E_b(\sigma)\|\le B$ for all real $\sigma$ with $1<\sigma<1+\delta$. The conclusion is that the function $\sigma\mapsto E_a(\sigma)$ on the reals does not tend to $0$ as $\sigma\to 1$ from the right.
--
--   This is the Mertens–de la Vallée Poussin inequality $3+4\cos\theta+\cos 2\theta\ge 0$ isolated as a statement of pure analysis: no characters or adelic input occurs, all arithmetic entering through the three bounds on the auxiliary Euler products. It is used in the non-vanishing step for Hecke $L$-functions of unitary characters, via [`NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar`](thm.html#NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Filter Topology

theorem NumberField.not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (a b : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ)
    (hab : ∀ v, (‖a v‖ = 1 ∧ b v = a v ^ 2) ∨ (a v = 0 ∧ ‖b v‖ ≤ 1))
    (hζ : ∃ C δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤ C / (σ - 1))
    (ha : ∃ U ∈ 𝓝 (1 : ℂ), ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧
      ∀ s ∈ U, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
    (hb : ∃ B δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - b v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤ B) :
    ¬ Tendsto
        (fun σ : ℝ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)
        (𝓝[>] 1) (𝓝 0) := by sorry
