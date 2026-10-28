-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_simpleIntegral_mul_eq_zero_readable
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_simpleIntegral_mul_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:55.826576+00:00
-- url     : https://prove2.me/theorems/86d5362c-5613-4331-b577-05629cdbfba1
-- title:
--   Orthogonality of Simple Integrals on Distinct Coordinates
-- statement:
--   This is the orthogonality statement for elementary stochastic integrals against distinct Brownian coordinates.
--
--   Let $W$ be a $d$-dimensional Brownian motion with distinct coordinates $i\ne j$, and let $\mathcal F$ be a common Brownian filtration. Let $H$ and $K$ be simple predictable integrands with strongly measurable coefficients at their respective partition start times. For arbitrary $t,t'\in\mathbb R$,
--   $$
--   \int \texttt{simpleIntegral}(W^i,H,t)\,\texttt{simpleIntegral}(W^j,K,t')\,dP=0.
--   $$
--
--   This is the finite-partition orthogonality result used before passing to general stochastic integrals by $L^2$ approximation.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_simpleIntegral_mul_eq_zero (W : MultidimBrownianMotion P d)
--       {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
--       (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {TH TK : ℝ}
--       (H : SimplePredictable Ω TH)
--       (K : SimplePredictable Ω TK)
--       (hH : ∀ a : Fin H.N, StronglyMeasurable[ℱ (H.partition a.castSucc)] (H.ξ a))
--       (hK : ∀ b : Fin K.N, StronglyMeasurable[ℱ (K.partition b.castSucc)] (K.ξ b))
--       (t t' : ℝ) :
--       ∫ ω, simpleIntegral (W.W i) H t ω * simpleIntegral (W.W j) K t' ω ∂P = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossOrthogonalityLimit`](https://prove2.me/theorems/0a6cdcb3-be60-427a-8dc0-4862ed142b74).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb).
--
--   Supporting theorems: [`integrable_and_integral_cross_clamped`](https://prove2.me/theorems/79cd0607-bfb0-45c8-8086-36a38db2872c).
--
--   Previous: [`integrable_and_integral_cross_clamped`](https://prove2.me/theorems/79cd0607-bfb0-45c8-8086-36a38db2872c) · Next: [`memLp_simpleIntegral`](https://prove2.me/theorems/7c5f50d8-edb5-487c-a4bf-6c19ad9a378c).
--
--   [Source excerpt, lines 240–248](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L240-L248) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L238-L285 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossOrthogonalityLimit`, declaration `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_simpleIntegral_mul_eq_zero`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
open LevyStochCalc.Brownian.Ito

theorem LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_simpleIntegral_mul_eq_zero_readable (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {TH TK : ℝ}
    (H : SimplePredictable Ω TH)
    (K : SimplePredictable Ω TK)
    (hH : ∀ a : Fin H.N, StronglyMeasurable[ℱ (H.partition a.castSucc)] (H.ξ a))
    (hK : ∀ b : Fin K.N, StronglyMeasurable[ℱ (K.partition b.castSucc)] (K.ξ b))
    (t t' : ℝ) :
    ∫ ω, simpleIntegral (W.W i) H t ω * simpleIntegral (W.W j) K t' ω ∂P = 0 := by sorry
