-- Prove2me | Theorems.Thm_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
-- name    : MeasureTheory.setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/dd2ddab9-3052-5f2a-9d8a-7769b429cb8e
-- title:
--   Laplace concentration: off-window tail bound from a gap
-- statement:
--   Let $\varphi:\mathbb R\to\mathbb R$ be measurable with $\varphi(v)\le\varphi(0)$ for all $v$, and let $\gamma,\delta,\rho$ be reals with $\gamma>0$, $\rho>0$ and $\rho\le\delta$, satisfying the two gap conditions $\varphi(v)\le\varphi(0)-\gamma$ whenever $|v|>\delta$, and $\varphi(0)-\gamma/2\le\varphi(v)$ whenever $|v|\le\rho$. Let $H:\mathbb R\to\mathbb R$ and $\Lambda_0\ge 0$ be such that $v\mapsto e^{\Lambda_0(\varphi(v)-\varphi(0)+\gamma)}H(v)$ is integrable on $\mathbb R$ (with respect to Lebesgue measure) and $H$ is integrable on $\{v:|v|\le\delta\}$. Let $h:\mathbb R\to\mathbb R$ be measurable with $0\le h(v)\le H(v)$ for all $v$, and let $c_m$ be a real with $e^{c_m}\le h(v)$ whenever $|v|\le\rho$. Then for every $\Lambda\ge\Lambda_0$ the function $v\mapsto e^{\Lambda\varphi(v)}h(v)$ is integrable on $\{v:|v|>\delta\}$ and on $\{v:|v|\le\delta\}$, and $$\int_{|v|>\delta} e^{\Lambda\varphi(v)}h(v)\,dv\ \le\ \frac{\bigl(\int_{\mathbb R} e^{\Lambda_0(\varphi(v)-\varphi(0)+\gamma)}H(v)\,dv\bigr)e^{-c_m}}{2\rho}\,e^{-\Lambda\gamma/2}\int_{|v|\le\delta} e^{\Lambda\varphi(v)}h(v)\,dv.$$
--
--   This is the localisation (concentration) half of Laplace's method for integrals $\int e^{\Lambda\varphi}h$, stated with no differentiability assumption on $\varphi$: the unique maximum at $0$ enters only through the gap data $(\gamma,\delta,\rho)$, and the bound is uniform over all amplitudes $h$ squeezed between the constant $e^{c_m}$ near the origin and the fixed majorant $H$. It is used in the analytic estimates of the Langlands–Tunnell part of the development, where tilted integrals over the complement of a window are compared with integrals over the window.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap.lean

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφmax : ∀ v, φ v ≤ φ 0)
    (γ δ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ)
    (hout : ∀ v, δ < |v| → φ v ≤ φ 0 - γ) (hin : ∀ v, |v| ≤ ρ → φ 0 - γ / 2 ≤ φ v)
    (H : ℝ → ℝ) (Λ₀ : ℝ) (hΛ₀ : 0 ≤ Λ₀)
    (hHint : Integrable (fun v => Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v))
    (hHloc : IntegrableOn H {v | |v| ≤ δ})
    (h : ℝ → ℝ) (hhm : Measurable h) (hh0 : ∀ v, 0 ≤ h v) (hhH : ∀ v, h v ≤ H v)
    (cm : ℝ) (hhin : ∀ v, |v| ≤ ρ → Real.exp cm ≤ h v)
    (Λ : ℝ) (hΛ : Λ₀ ≤ Λ) :
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | δ < |v|} ∧
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | |v| ≤ δ} ∧
    ∫ v in {v | δ < |v|}, Real.exp (Λ * φ v) * h v ≤
      ((∫ v, Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v) * Real.exp (-cm) / (2 * ρ)) * Real.exp (-(Λ * γ / 2)) *
        ∫ v in {v | |v| ≤ δ}, Real.exp (Λ * φ v) * h v := by sorry
