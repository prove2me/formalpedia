-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_ae_add_eq_of_integral_mul_fderiv_eq_zero_readable
-- name    : FunctionalInequalities.Energy.Euclidean.ae_add_eq_of_integral_mul_fderiv_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:19.868401+00:00
-- url     : https://prove2.me/theorems/41fc0968-9c28-44e9-bc3c-b52d1929e169
-- title:
--   Translation Invariance From Vanishing Weak Derivatives
-- statement:
--   This is a distributional translation-invariance statement for a locally integrable function.
--
--   Let $V$ be a finite-dimensional real inner-product normed additive group equipped with its Borel measurable structure and a second-countable topology. Let $m$ be an additive Haar measure on $V$, and let $h:V\to\mathbb R$ be locally integrable with respect to $m$. Assume that for every smooth compactly supported test function $\varphi:V\to\mathbb R$ and every direction $w\in V$,
--
--   $$
--   \int h(x)\,D\varphi(x)[w]\,dm(x)=0.
--   $$
--
--   Then, for every translation vector $v\in V$, $h$ is invariant under translation by $v$ almost everywhere:
--
--   $$
--   \forall v\in V,\qquad h(x+v)=h(x)\quad\text{for $m$-almost every }x.
--   $$
--
--   The Lean declaration is `ae_add_eq_of_integral_mul_fderiv_eq_zero_readable`; the values are real, and the conclusion is an a.e. equality for each fixed translation vector. This is an auxiliary weak-gradient result and does not itself assert that $h$ is almost everywhere constant.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.Euclidean`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_add_eq_of_integral_mul_fderiv_eq_zero {h : V → ℝ} (hh : LocallyIntegrable h m)
--       (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
--         ∫ x, h x * fderiv ℝ φ x w ∂m = 0)
--       (v : V) :
--       ∀ᵐ x ∂m, h (x + v) = h x
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/ZeroGradient`](https://prove2.me/theorems/52f28c92-8879-4a35-be78-f95c88a2a467).
--
--   Supporting theorems: [`integral_mul_sub_translate_eq_zero`](https://prove2.me/theorems/92d2bdd3-6571-4798-95e4-ba80de2514d6), [`locallyIntegrable_comp_add_right`](https://prove2.me/theorems/20004fc3-1194-490c-af8c-f5c2147ffe0b).
--
--   Previous: [`locallyIntegrable_comp_add_right`](https://prove2.me/theorems/20004fc3-1194-490c-af8c-f5c2147ffe0b) · Next: [`exists_ae_eq_const_of_measurable_of_forall_ae_add_eq`](https://prove2.me/theorems/582959f3-9760-49aa-8308-fec3d495a4ec).
--
--   [Source excerpt, lines 277–281](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L277-L281) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L276-L328 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.ae_add_eq_of_integral_mul_fderiv_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient

open MeasureTheory Filter Topology
open scoped ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Energy.Euclidean.ae_add_eq_of_integral_mul_fderiv_eq_zero_readable {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0)
    (v : V) :
    ∀ᵐ x ∂m, h (x + v) = h x := by sorry
