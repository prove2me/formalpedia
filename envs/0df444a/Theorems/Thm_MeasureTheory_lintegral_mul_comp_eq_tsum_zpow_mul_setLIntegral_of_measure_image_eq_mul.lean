-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul
-- name    : MeasureTheory.lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/13ed1957-6be6-5347-b450-4af6e8e54c5a
-- title:
--   Peeling a geometric shell index off a lower Lebesgue integral
-- statement:
--   Let $Q$ be a measurable space and $\nu$ a measure on it, let $T : Q \to Q$ be a measurable equivalence (a measurable bijection with measurable inverse), and let $\kappa \in [0,\infty]$ satisfy $\kappa \neq 0$ and $\kappa \neq \infty$. Assume $\nu(T(s)) = \kappa \cdot \nu(s)$ for every measurable $s \subseteq Q$. Let $m : Q \to \mathbb{Z}$ be measurable with $m(Tq) = m(q) + 1$ for all $q$, and let $h : Q \to [0,\infty]$ be measurable with $h(Tq) = h(q)$ for all $q$. Then for every function $\Phi : \mathbb{Z} \to [0,\infty]$, with no measurability or convergence hypothesis on $\Phi$, the lower Lebesgue integrals satisfy $$\int_Q h(q)\,\Phi(m(q))\,d\nu(q) = \Big(\sum_{n \in \mathbb{Z}} \kappa^{n}\,\Phi(n)\Big)\cdot \int_{\{q \,:\, m(q) = 0\}} h\,d\nu,$$ where $\kappa^{n}$ is the integer power in $[0,\infty]$ and the sum is the unconditional sum of a family of elements of $[0,\infty]$. Both sides are allowed to be $0$ or $\infty$, all arithmetic being that of $[0,\infty]$.
--
--   This is the abstract form of peeling off one Euler factor: an automorphism scaling the measure by a constant factor $\kappa$ and shifting an integer shell index by one turns an integral of $h \cdot (\Phi \circ m)$ into a geometric-type series in $\kappa$ times the integral of $h$ over the zeroth shell. It is used for integrals over quotients of a group by the Haar-measure computation [`HaarQuotient.lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer`](thm.html#HaarQuotient.lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer), where $T$ is translation by an element normalising the subgroup and $\kappa$ its modulus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul
    {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) (T : Q ≃ᵐ Q)
    (κ : ℝ≥0∞) (hκ₀ : κ ≠ 0) (hκ : κ ≠ ∞)
    (hT : ∀ s : Set Q, MeasurableSet s → ν (T '' s) = κ * ν s)
    (m : Q → ℤ) (hm : Measurable m) (hmT : ∀ q, m (T q) = m q + 1)
    (h : Q → ℝ≥0∞) (hh : Measurable h) (hhT : ∀ q, h (T q) = h q)
    (Φ : ℤ → ℝ≥0∞) :
    ∫⁻ q, h q * Φ (m q) ∂ν = (∑' n : ℤ, κ ^ n * Φ n) * ∫⁻ q in {q | m q = 0}, h q ∂ν := by sorry
