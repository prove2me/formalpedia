-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_stochasticIntegral_mul_eq_zero_readable
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:10.168356+00:00
-- url     : https://prove2.me/theorems/a9eee61c-6570-4194-86d3-3b8045d9de2c
-- title:
--   Orthogonality of Itô Integrals on Distinct Brownian Coordinates
-- statement:
--   This is the orthogonality identity for Itô integrals driven by distinct coordinates of a multidimensional Brownian motion.
--
--   Let $W$ be a $d$-dimensional Brownian motion, let $i\ne j$, and let $\mathcal F$ be a common Brownian filtration. Let $H$ and $K$ be measurable and progressively measurable integrands whose integrated squared norms are finite in $\mathrm{ENNReal}$ on every positive interval. For $t\ge0$, the corresponding scalar Itô integrals satisfy
--   $$
--   \int I^i_t(\omega)I^j_t(\omega)\,dP=0,
--   $$
--   where $I^i_t=\texttt{stochasticIntegral}(W^i,\mathcal F,H,t)$ and $I^j_t=\texttt{stochasticIntegral}(W^j,\mathcal F,K,t)$.
--
--   The statement is the general orthogonality result obtained from elementary-integrand orthogonality and $L^2$ convergence.
--
--   **Formalization Note** The square-integrability hypotheses are expressed through `MemLp` in the supporting declarations, while the integrand assumptions use $\mathrm{ENNReal}$ lower integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_stochasticIntegral_mul_eq_zero (W : MultidimBrownianMotion P d)
--       {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
--       (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
--       {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
--       (hHp : Probability.ProgressivelyMeasurable ℱ H)
--       (hHs : ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hKm : Measurable (Function.uncurry K))
--       (hKp : Probability.ProgressivelyMeasurable ℱ K)
--       (hKs : ∀ T : ℝ, 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {t : ℝ} (ht : 0 ≤ t) :
--       ∫ ω, stochasticIntegral (W.W i) ℱ (hcoord i) H hHm hHp hHs t ω
--         * stochasticIntegral (W.W j) ℱ (hcoord j) K hKm hKp hKs t ω ∂P = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossOrthogonalityLimit`](https://prove2.me/theorems/0a6cdcb3-be60-427a-8dc0-4862ed142b74).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionApi`](https://prove2.me/theorems/2726bba3-f240-429d-9052-e494c979e1f0), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`integral_mul_eq_zero_of_tendsto_eLpNorm`](https://prove2.me/theorems/9e82e98b-0377-41ae-b977-70c8c0709ea7), [`integral_simpleIntegral_mul_eq_zero`](https://prove2.me/theorems/86d5362c-5613-4331-b577-05629cdbfba1), [`memLp_simpleIntegral`](https://prove2.me/theorems/7c5f50d8-edb5-487c-a4bf-6c19ad9a378c).
--
--   Previous: [`integral_mul_eq_zero_of_tendsto_eLpNorm`](https://prove2.me/theorems/9e82e98b-0377-41ae-b977-70c8c0709ea7).
--
--   [Source excerpt, lines 371–384](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L371-L384) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L370-L399 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossOrthogonalityLimit`, declaration `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
open LevyStochCalc.Brownian.Ito

theorem LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero_readable (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, stochasticIntegral (W.W i) ℱ (hcoord i) H hHm hHp hHs t ω
      * stochasticIntegral (W.W j) ℱ (hcoord j) K hKm hKp hKs t ω ∂P = 0 := by sorry
