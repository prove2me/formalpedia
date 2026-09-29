-- Prove2me | Theorems.Thm_MeasureTheory_exists_clm_opNorm_le_noAtomicMass_apply_eq_tsum_integral_mul_fourier_of_summable_of_ae_measure_fibre_eq_zero
-- name    : MeasureTheory.exists_clm_opNorm_le_noAtomicMass_apply_eq_tsum_integral_mul_fourier_of_summable_of_ae_measure_fibre_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/a615aeec-e041-5b23-966a-fd3a96a9f0b5
-- title:
--   A winding functional on Tᵈ: norm, no atoms, Fourier values
-- statement:
--   Let $a,d$ be natural numbers, let $Y$ be a topological space with a measurable structure in which open sets are measurable, let $\mathrm{vol}$ be a measure on $Y$, let $m$ be a probability measure on the torus $\mathbb{T}^d=(\mathbb{R}/\mathbb{Z})^d$ (written `Fin d → AddCircle (1 : ℝ)`), and let $n_0\in\mathbb{Z}^d$. For each $\kappa\in\mathbb{Z}^a$ let $P_\kappa\colon Y\to\mathbb{T}^d$ be continuous and $c_\kappa\colon Y\to\mathbb{C}$ be continuous and $\mathrm{vol}$-integrable, and assume $\kappa\mapsto\int_Y\|c_\kappa\|\,d\mathrm{vol}$ is summable, and that for every $\tau\in\mathbb{T}^d$ and every $\kappa$ one has, for $\mathrm{vol}$-almost every $y$, $m\{q: P_\kappa(y)+q=\tau\}=0$. Then there is a continuous $\mathbb{C}$-linear functional $\mu$ on $C(\mathbb{T}^d,\mathbb{C})$ such that: (i) $\|\mu\|\le\sum_{\kappa}\int_Y\|c_\kappa\|\,d\mathrm{vol}$; (ii) for every $\tau\in\mathbb{T}^d$ and every $\varepsilon>0$ there are open sets $U_i\subseteq\mathbb{R}/\mathbb{Z}$ with $\tau_i\in U_i$ such that every continuous $g$ with $\|g\|_\infty\le 1$ vanishing at every $\theta$ with some $\theta_i\notin U_i$ satisfies $\|\mu(g)\|<\varepsilon$; and (iii) for every $n\in\mathbb{Z}^d$ and every continuous $e$ with $e(\theta)=\prod_i \mathrm{fourier}_{n_i}(\theta_i)$,
--   $$\mu(e)=\sum_{\kappa}\int_Y c_\kappa(y)\Bigl(\prod_i \mathrm{fourier}_{n_i-n_{0,i}}(P_\kappa(y)_i)\Bigr)\Bigl(\int_{\mathbb{T}^d}\prod_i \mathrm{fourier}_{n_i-n_{0,i}}(q_i)\,dm(q)\Bigr)d\mathrm{vol}(y).$$
--
--   This is the construction of a measure-like functional on the $d$-torus attached to an absolutely summable family of continuous amplitudes $c_\kappa$ and continuous frequency maps $P_\kappa$, together with its total-variation bound, the statement that it carries no atomic mass at any point, and the evaluation of its Fourier coefficients. It is used as the analytic engine for the corresponding statement about Schwartz data, where the fibrewise summation over $\kappa$ is recorded as a `HasSum`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_clm_opNorm_le_noAtomicMass_apply_eq_tsum_integral_mul_fourier_of_summable_of_ae_measure_fibre_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_clm_opNorm_le_noAtomicMass_apply_eq_tsum_integral_mul_fourier_of_summable_of_ae_measure_fibre_eq_zero
    (a d : ℕ) (Y : Type) [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (vol : Measure Y) (m : Measure (Fin d → AddCircle (1 : ℝ))) [IsProbabilityMeasure m]
    (n₀ : Fin d → ℤ) (P : (Fin a → ℤ) → Y → (Fin d → AddCircle (1 : ℝ))) (hP : ∀ κ, Continuous (P κ))
    (c : (Fin a → ℤ) → Y → ℂ) (hcc : ∀ κ, Continuous (c κ)) (hci : ∀ κ, Integrable (c κ) vol)
    (hcs : Summable fun κ => ∫ y, ‖c κ y‖ ∂vol)
    (hfib : ∀ (τ : Fin d → AddCircle (1 : ℝ)) (κ : Fin a → ℤ),
      ∀ᵐ y ∂vol, m {q : Fin d → AddCircle (1 : ℝ) | P κ y + q = τ} = 0) :
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      ‖μ‖ ≤ ∑' κ, ∫ y, ‖c κ y‖ ∂vol ∧
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) →
        μ e = ∑' κ, ∫ y, c κ y * ((∏ i, fourier (n i - n₀ i) (P κ y i)) *
          ∫ q, ∏ i, fourier (n i - n₀ i) (q i) ∂m) ∂vol := by sorry
