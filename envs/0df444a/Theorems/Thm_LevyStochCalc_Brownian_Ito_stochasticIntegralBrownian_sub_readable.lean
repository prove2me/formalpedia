-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_sub_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:57.335172+00:00
-- url     : https://prove2.me/theorems/a954497d-231b-4ebc-910f-e11817f51410
-- title:
--   Subtractive Linearity of the Itô Integral
-- statement:
--   This proves subtractive linearity of the Brownian Itô integral.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space with Brownian motion $W$ and Brownian filtration $\mathcal F$. Let $H_1,H_2:\Omega\times\mathbb R\to\mathbb R$. Assume each of $H_1$, $H_2$, and $H_1-H_2$ is jointly measurable, progressively measurable, and has finite `ENNReal` energy on every positive horizon:
--   $$
--   \int_\Omega\int_{[0,T]}\|H_i(\omega,s)\|_+^2\,ds\,dP<\top
--   \quad(i=1,2),
--   $$
--   with the analogous condition for $H_1-H_2$.
--
--   For every $T>0$,
--   $$
--   I_T[H_1-H_2](\omega)
--   =I_T[H_1](\omega)-I_T[H_2](\omega)
--   $$
--   for $P$-almost every $\omega$.
--
--   The result is a basic linearity rule for later finite-sum constructions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_sub {H₁ H₂ : Ω → ℝ → ℝ}
--       (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
--       (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
--       (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
--       (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hms : Measurable (Function.uncurry fun ω s => H₁ ω s - H₂ ω s))
--       (hps : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s - H₂ ω s)
--       (hqs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {T : ℝ} (hT : 0 < T) :
--       stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s - H₂ ω s) hms hps hqs T
--         =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
--           - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFinsetSum`](https://prove2.me/theorems/3c65a1ac-837e-48a1-b323-dc87feeb6397).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`stochasticIntegralBrownian_add`](https://prove2.me/theorems/63f87c77-88d3-49b3-b12f-0856c509d6a6), [`stochasticIntegralBrownian_neg`](https://prove2.me/theorems/5492f889-dcf9-4710-b8c2-bd3dcd30d16a).
--
--   Previous: [`stochasticIntegralBrownian_neg`](https://prove2.me/theorems/5492f889-dcf9-4710-b8c2-bd3dcd30d16a) · Next: [`exists_stochasticIntegralBrownian_finsetSum`](https://prove2.me/theorems/b0d141d4-c156-4326-80cf-9bf508518511).
--
--   [Source excerpt, lines 74–89](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFinsetSum.lean#L74-L89) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFinsetSum.lean#L72-L120 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFinsetSum`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFinsetSum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFinsetSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub_readable {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hms : Measurable (Function.uncurry fun ω s => H₁ ω s - H₂ ω s))
    (hps : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s - H₂ ω s)
    (hqs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s - H₂ ω s) hms hps hqs T
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
        - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω := by sorry
