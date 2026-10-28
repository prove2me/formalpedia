-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_masterApprox_compensator_tendsto_L1_readable
-- name    : LevyStochCalc.Brownian.Ito.masterApprox_compensator_tendsto_L1_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:58.228266+00:00
-- url     : https://prove2.me/theorems/9528fd58-b2a9-4848-86d2-1d31e25f342a
-- title:
--   Master Approximation Compensator Convergence
-- statement:
--   Let $P$ be a probability measure, let $\mathcal F$ be a filtration, and let $H:\Omega\times\mathbb R\to\mathbb R$ be measurable and progressively measurable. Assume that for every $T>0$, the joint nonnegative integral of $|H|^2$ over $\Omega\times[0,T]$ is strictly below $\infty$. For each $n$, let $G_n=\mathrm{masterApprox}(\mathcal F,H,\ldots,n)$ be the associated simple approximation. For every $t\ge0$,
--
--   $$\left\|\omega\mapsto\int_{[0,t]}G_n.\mathrm{eval}(u,\omega)^2\,du-
--   \int_{[0,t]}H(\omega,u)^2\,du\right\|_{L^1(P)}\longrightarrow0.$$
--
--   The conclusion is a convergence statement in the extended $L^1$ norm; the approximation and its hypotheses are the named Lean definitions `masterApprox` and `ProgressivelyMeasurable`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma masterApprox_compensator_tendsto_L1 {t : ℝ} (ht : 0 ≤ t) :
--       Filter.Tendsto (fun n => MeasureTheory.eLpNorm
--         (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
--             ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
--           - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P)
--         Filter.atTop (nhds 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionQuadVar`](https://prove2.me/theorems/6062fba0-aa8d-4423-8c5c-de5c7abb85aa).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f).
--
--   Supporting theorems: [`tendsto_eLpNorm_one_sq_sub`](https://prove2.me/theorems/f09a6b4b-92fc-4d7f-afe6-745f7f468f5b).
--
--   Next: [`martingale_quadVar_stochasticIntegralBrownian`](https://prove2.me/theorems/26bd8fe9-dab1-4af9-8f99-4684a48699d4).
--
--   [Source excerpt, lines 331–336](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean#L331-L336) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean#L326-L429 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionQuadVar`, declaration `LevyStochCalc.Brownian.Ito.masterApprox_compensator_tendsto_L1`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include h_meas h_progMeas h_sq_int_global

lemma LevyStochCalc.Brownian.Ito.masterApprox_compensator_tendsto_L1_readable {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
          ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P)
      Filter.atTop (nhds 0) := by sorry
