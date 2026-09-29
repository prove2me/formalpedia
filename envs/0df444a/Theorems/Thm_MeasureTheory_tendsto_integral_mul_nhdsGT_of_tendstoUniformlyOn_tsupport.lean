-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport
-- name    : MeasureTheory.tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/195756bd-6d52-5d80-9d48-1c731153b3ef
-- title:
--   Dominated convergence for integrals against a compactly supported weight
-- statement:
--   Let $X$ be a topological space equipped with a measurable structure for which the open sets are measurable, and let $\mu$ be a measure on $X$ that is finite on compact sets. Let $w : X \to \mathbb{R}$ be measurable, with compact support in the topological sense (`HasCompactSupport`), and globally bounded in the sense that there is $B \in \mathbb{R}$ with $|w(x)| \le B$ for all $x$. Let $\Phi : \mathbb{R} \to X \to \mathbb{C}$ and $\Phi_0 : X \to \mathbb{C}$ be such that each $\Phi(\theta)$ and $\Phi_0$ are almost everywhere strongly measurable with respect to $\mu$, such that $\|\Phi_0(x)\| \le B_0$ for some constant $B_0$ and all $x$ in the topological support $\operatorname{tsupport} w$, and such that $\Phi(\theta) \to \Phi_0$ uniformly on $\operatorname{tsupport} w$ as $\theta \to 0$ within $(0,\infty)$. Then $\int_X \Phi(\theta)(x)\, w(x)\, d\mu(x) \to \int_X \Phi_0(x)\, w(x)\, d\mu(x)$ as $\theta \to 0^{+}$, the real-valued $w$ being coerced into $\mathbb{C}$ in both integrals.
--
--   This is the Lebesgue dominated convergence theorem in the shape needed to pass a limit through an integral against a fixed bounded compactly supported weight, the limit being taken along the filter of right-hand neighbourhoods of $0$. It is used in the archimedean comparison of twisted orbital integrals, where $w$ is a section function for a quotient by a centraliser and $\Phi(\theta)$ is a test function evaluated at a one-parameter family of twisted conjugates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter

theorem MeasureTheory.tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (w : X → ℝ) (hwm : Measurable w) (hwc : HasCompactSupport w) (hwb : ∃ B : ℝ, ∀ x, |w x| ≤ B)
    (Φ : ℝ → X → ℂ) (Φ₀ : X → ℂ)
    (hΦm : ∀ θ : ℝ, AEStronglyMeasurable (Φ θ) μ) (hΦ₀m : AEStronglyMeasurable Φ₀ μ)
    (hΦ₀b : ∃ B₀ : ℝ, ∀ x ∈ tsupport w, ‖Φ₀ x‖ ≤ B₀)
    (hunif : TendstoUniformlyOn Φ Φ₀ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (tsupport w)) :
    Tendsto (fun θ : ℝ => ∫ x, Φ θ x * (w x : ℂ) ∂μ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x, Φ₀ x * (w x : ℂ) ∂μ)) := by sorry
