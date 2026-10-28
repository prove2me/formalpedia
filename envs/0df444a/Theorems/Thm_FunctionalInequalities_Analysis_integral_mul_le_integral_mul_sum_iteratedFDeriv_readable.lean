-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_le_integral_mul_sum_iteratedFDeriv_readable
-- name    : FunctionalInequalities.Analysis.integral_mul_le_integral_mul_sum_iteratedFDeriv_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:41.018561+00:00
-- url     : https://prove2.me/theorems/a34ffeae-071d-4fec-b551-07733fa204a2
-- title:
--   Fatou Bound for Convex Second Differences
-- statement:
--   This is the Fatou bound for the distributional second derivatives of a convex function.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be convex, let $\iota$ be a finite type, let $v_i\in E$ and $c_i\geq0$ for $i\in\iota$. Let $\chi:E\to\mathbb R$ be nonnegative, $C^2$, and compactly supported. Let $g:E\to\mathbb R$ be almost everywhere strongly measurable. Assume that, almost everywhere in $x$, for every $\varepsilon>0$ there is $\delta>0$ such that for $0<t<\delta$,
--
--   $$
--   g(x)-\varepsilon\leq\sum_i c_i\frac{u(x+t v_i)+u(x-t v_i)-2u(x)}{t^2}.
--   $$
--
--   Then
--
--   $$
--   \int g\,\chi\,dx
--   \leq
--   \int u(x)\sum_i c_i\,D^2\chi(x)[v_i,v_i] \,dx.
--   $$
--
--   This is an auxiliary distributional inequality used to integrate lower bounds for second differences against nonnegative test functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_le_integral_mul_sum_iteratedFDeriv [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {ι : Type*} [Fintype ι] (v : ι → E) {c : ι → ℝ}
--       (hc : ∀ i, 0 ≤ c i) {χ : E → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
--       (hχ0 : ∀ x, 0 ≤ χ x) {g : E → ℝ} (hgm : AEStronglyMeasurable g (volume : Measure E))
--       (hg : ∀ᵐ x ∂(volume : Measure E), ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
--         g x - ε ≤ ∑ i, c i * ((u (x + t • v i) + u (x - t • v i) - 2 * u x) / t ^ 2)) :
--       ∫ x, g x * χ x ≤ ∫ x, u x * ∑ i, c i * iteratedFDeriv ℝ 2 χ x (fun _ => v i)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/SecondOrder`](https://prove2.me/theorems/25ef7ab1-0f22-4192-9c58-d196bc21f161).
--
--   Supporting theorems: [`tendsto_integral_secondDifference_mul`](https://prove2.me/theorems/4354b6fd-00d6-4dd4-9dfb-0b7b24838470).
--
--   Previous: [`tendsto_integral_secondDifference_mul`](https://prove2.me/theorems/4354b6fd-00d6-4dd4-9dfb-0b7b24838470) · Next: [`ae_exists_secondOrder_expansion`](https://prove2.me/theorems/5eb08b15-cdd6-4026-aca8-c20821e30f23).
--
--   [Source excerpt, lines 462–468](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L462-L468) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L459-L577 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondOrder`, declaration `FunctionalInequalities.Analysis.integral_mul_le_integral_mul_sum_iteratedFDeriv`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder

open MeasureTheory Set Filter
variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.integral_mul_le_integral_mul_sum_iteratedFDeriv_readable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {ι : Type*} [Fintype ι] (v : ι → E) {c : ι → ℝ}
    (hc : ∀ i, 0 ≤ c i) {χ : E → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) {g : E → ℝ} (hgm : AEStronglyMeasurable g (volume : Measure E))
    (hg : ∀ᵐ x ∂(volume : Measure E), ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      g x - ε ≤ ∑ i, c i * ((u (x + t • v i) + u (x - t • v i) - 2 * u x) / t ^ 2)) :
    ∫ x, g x * χ x ≤ ∫ x, u x * ∑ i, c i * iteratedFDeriv ℝ 2 χ x (fun _ => v i) := by sorry
