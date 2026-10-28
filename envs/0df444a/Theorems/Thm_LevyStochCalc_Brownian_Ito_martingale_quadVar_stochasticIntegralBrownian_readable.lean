-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_quadVar_stochasticIntegralBrownian_readable
-- name    : LevyStochCalc.Brownian.Ito.martingale_quadVar_stochasticIntegralBrownian_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:38.504982+00:00
-- url     : https://prove2.me/theorems/26bd8fe9-dab1-4af9-8f99-4684a48699d4
-- title:
--   Compensated Square Martingale for the Itô Integral
-- statement:
--   Let $P$ be a probability measure, $W$ a Brownian motion, and $\mathcal F$ a Brownian filtration. Let $H:\Omega\times\mathbb R\to\mathbb R$ be measurable and progressively measurable, and assume that for every $T>0$ the joint $L^2$ integral of $H$ over $[0,T]$ is finite. Then the process
--
--   $$t\longmapsto \mathrm{stochasticIntegralBrownian}(W,\mathcal F,H,t)^2-
--   \int_{[0,t]}H(\cdot,u)^2\,du$$
--
--   is a martingale with respect to $\mathcal F$ and $P$. This is the general-integrand counterpart of the simple-level compensated-square martingale.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma martingale_quadVar_stochasticIntegralBrownian :
--       MeasureTheory.Martingale
--         (fun t ω => (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
--           - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
--         ℱ P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionQuadVar`](https://prove2.me/theorems/6062fba0-aa8d-4423-8c5c-de5c7abb85aa).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`martingale_simpleIntegral_sq_sub_compensator`](https://prove2.me/theorems/76ba9e80-d221-4784-b289-e962828cbbfd), [`masterApprox_compensator_tendsto_L1`](https://prove2.me/theorems/9528fd58-b2a9-4848-86d2-1d31e25f342a), [`setIntegral_eval_sq_Icc_clamped`](https://prove2.me/theorems/264a25e4-219e-44a6-9deb-bfc553ff7dd9), [`tendsto_eLpNorm_one_sq_sub`](https://prove2.me/theorems/f09a6b4b-92fc-4d7f-afe6-745f7f468f5b).
--
--   Previous: [`masterApprox_compensator_tendsto_L1`](https://prove2.me/theorems/9528fd58-b2a9-4848-86d2-1d31e25f342a).
--
--   [Source excerpt, lines 438–442](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean#L438-L442) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean#L431-L553 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionQuadVar`, declaration `LevyStochCalc.Brownian.Ito.martingale_quadVar_stochasticIntegralBrownian`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
include h_meas h_progMeas h_sq_int_global hℱ

lemma LevyStochCalc.Brownian.Ito.martingale_quadVar_stochasticIntegralBrownian_readable :
    MeasureTheory.Martingale
      (fun t ω => (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      ℱ P := by sorry
