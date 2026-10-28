-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_congr_of_pos_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:55.568011+00:00
-- url     : https://prove2.me/theorems/7c8a7f3d-a1b5-4c44-b668-4100f7891904
-- title:
--   Positive-Time Congruence of Itô Integrals
-- statement:
--   Let $W$ be a Brownian motion with Brownian filtration. Let $H₁,H₂:Ω×ℝ→ℝ$ each be jointly measurable, progressively measurable, and of finite squared `ENNReal` energy on every positive time interval. Assume that
--
--   $$H₁(ω,s)=H₂(ω,s)\quad\text{whenever }s>0$$
--
--   for every $ω∈Ω$. Then, for every $t>0$,
--
--   $$\int_0^t H₁\,dW=\int_0^t H₂\,dW\quad P\text{-almost everywhere}.$$
--
--   The theorem does not require equality at time $s=0$ or at negative times. It formalizes that the positive-time Itô integral is insensitive to the integrand outside $(0,t]$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_congr_of_pos
--       {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
--       (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
--       (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hm₂ : Measurable (Function.uncurry H₂))
--       (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
--       (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → H₁ ω s = H₂ ω s)
--       {t : ℝ} (ht : 0 < t) :
--       stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t
--         =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoLocality`](https://prove2.me/theorems/24c85544-31a3-4ffd-a08e-f5b9ac9b8eba).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`stepIoc₀_eval`](https://prove2.me/theorems/2c0d5744-8278-417f-9f9c-dd287d9c0a4f), [`stochasticIntegralBrownian_indicator_Ioc`](https://prove2.me/theorems/bcc8c011-e83f-4b9e-a0e6-5de008451e39).
--
--   Previous: [`stochasticIntegralBrownian_stopped_eq_of_le`](https://prove2.me/theorems/dc8b0d30-1ce9-485a-bc89-a30aad33e6df) · Next: [`stochasticIntegralBrownian_congr_of_le`](https://prove2.me/theorems/b2a61bae-ccc8-42f5-8c56-486156033a8c).
--
--   [Source excerpt, lines 503–515](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLocality.lean#L503-L515) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLocality.lean#L502-L562 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLocality`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLocality

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos_readable
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t := by sorry
