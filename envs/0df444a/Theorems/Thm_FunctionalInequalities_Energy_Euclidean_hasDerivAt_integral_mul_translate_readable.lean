-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_hasDerivAt_integral_mul_translate_readable
-- name    : FunctionalInequalities.Energy.Euclidean.hasDerivAt_integral_mul_translate_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:26.454613+00:00
-- url     : https://prove2.me/theorems/578ccf2b-12bc-48b1-889e-1bee05d7af56
-- title:
--   Derivative of an Integral Against a Translated Test
-- statement:
--   This proves differentiation under the integral sign for translated test functions.
--
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $m$ be a measure on $V$, and let $h:V\to\mathbb R$ be locally integrable with respect to $m$. Let $\phi:V\to\mathbb R$ be smooth and compactly supported. For $v\in V$ and $t\in\mathbb R$, define
--
--   $$
--   F(s)=\int h(x)\phi(x-sv)\,dm(x).
--   $$
--
--   Then $F$ has derivative at $t$ equal to
--
--   $$
--   F'(t)=-\int h(x)D\phi(x-tv)v\,dm(x).
--   $$
--
--   Equivalently,
--
--   $$
--   \operatorname{HasDerivAt}\!\left(s\mapsto\int h(x)\phi(x-sv)\,dm(x),
--   -\int h(x)D\phi(x-tv)v\,dm(x),t\right).
--   $$
--
--   This is a technical differentiation lemma used to convert a weak derivative condition into translation identities.
--
--   **Formalization Note** The declaration does not assume that $m$ is an additive Haar measure.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.Euclidean`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasDerivAt_integral_mul_translate {h : V → ℝ} (hh : LocallyIntegrable h m) {φ : V → ℝ}
--       (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : V) (t : ℝ) :
--       HasDerivAt (fun s : ℝ => ∫ x, h x * φ (x - s • v) ∂m)
--         (-∫ x, h x * fderiv ℝ φ (x - t • v) v ∂m) t
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/ZeroGradient`](https://prove2.me/theorems/52f28c92-8879-4a35-be78-f95c88a2a467).
--
--   Supporting theorems: [`norm_mul_fderiv_comp_sub_smul_le`](https://prove2.me/theorems/ac853596-8eb4-4516-8eb3-374b5c046e01).
--
--   Previous: [`norm_mul_fderiv_comp_sub_smul_le`](https://prove2.me/theorems/ac853596-8eb4-4516-8eb3-374b5c046e01) · Next: [`integral_mul_sub_translate_eq_zero`](https://prove2.me/theorems/92d2bdd3-6571-4798-95e4-ba80de2514d6).
--
--   [Source excerpt, lines 89–92](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L89-L92) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L86-L161 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.hasDerivAt_integral_mul_translate`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient

open MeasureTheory Filter Topology
open scoped ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
omit [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Energy.Euclidean.hasDerivAt_integral_mul_translate_readable {h : V → ℝ} (hh : LocallyIntegrable h m) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, h x * φ (x - s • v) ∂m)
      (-∫ x, h x * fderiv ℝ φ (x - t • v) v ∂m) t := by sorry
