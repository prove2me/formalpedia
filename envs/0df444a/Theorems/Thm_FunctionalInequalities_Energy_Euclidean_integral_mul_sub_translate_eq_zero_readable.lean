-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_integral_mul_sub_translate_eq_zero_readable
-- name    : FunctionalInequalities.Energy.Euclidean.integral_mul_sub_translate_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:22.997804+00:00
-- url     : https://prove2.me/theorems/92d2bdd3-6571-4798-95e4-ba80de2514d6
-- title:
--   Vanishing Integral Difference Under a Zero Weak Gradient
-- statement:
--   This derives a translation identity from a zero weak gradient.
--
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $m$ be a measure on $V$, and let $h:V\to\mathbb R$ be locally integrable. Assume that for every smooth compactly supported test function $\psi$ and every direction $w\in V$,
--
--   $$
--   \int h(x)D\psi(x)w\,dm(x)=0.
--   $$
--
--   Then, for every smooth compactly supported $\phi$ and every $v\in V$,
--
--   $$
--   \int h(x)\bigl(\phi(x)-\phi(x-v)\bigr)\,dm(x)=0.
--   $$
--
--   The statement is an intermediate translation-invariance identity in the argument that a locally integrable function with zero weak gradient is almost everywhere constant.
--
--   **Formalization Note** The quantification over test functions includes the stated smoothness and compact-support hypotheses, and no Haar-measure assumption is required here.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.Euclidean`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_sub_translate_eq_zero {h : V → ℝ} (hh : LocallyIntegrable h m)
--       (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
--         ∫ x, h x * fderiv ℝ φ x w ∂m = 0)
--       {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : V) :
--       ∫ x, h x * (φ x - φ (x - v)) ∂m = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/ZeroGradient`](https://prove2.me/theorems/52f28c92-8879-4a35-be78-f95c88a2a467).
--
--   Supporting theorems: [`hasDerivAt_integral_mul_translate`](https://prove2.me/theorems/578ccf2b-12bc-48b1-889e-1bee05d7af56).
--
--   Previous: [`hasDerivAt_integral_mul_translate`](https://prove2.me/theorems/578ccf2b-12bc-48b1-889e-1bee05d7af56) · Next: [`locallyIntegrable_comp_add_right`](https://prove2.me/theorems/20004fc3-1194-490c-af8c-f5c2147ffe0b).
--
--   [Source excerpt, lines 165–169](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L165-L169) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L163-L248 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.integral_mul_sub_translate_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient

open MeasureTheory Filter Topology
open scoped ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
omit [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Energy.Euclidean.integral_mul_sub_translate_eq_zero_readable {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : V) :
    ∫ x, h x * (φ x - φ (x - v)) ∂m = 0 := by sorry
