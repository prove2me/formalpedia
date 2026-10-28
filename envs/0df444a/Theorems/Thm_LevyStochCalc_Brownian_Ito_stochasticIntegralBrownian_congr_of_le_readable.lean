-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_congr_of_le_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:06.007265+00:00
-- url     : https://prove2.me/theorems/b2a61bae-ccc8-42f5-8c56-486156033a8c
-- title:
--   Local Congruence of Itô Integrals
-- statement:
--   This proves that two integrands agreeing before a stopping time yield the same integral before that stopping time.
--
--   Let $\tau$ be a stopping time for a filtration $\mathcal F$ supporting a Brownian motion $W$. Let $H_1,H_2:\Omega\times\mathbb R\to\mathbb R$ be jointly measurable and progressively measurable, and assume that each has finite `ENNReal` energy on every positive horizon. Suppose that for every $\omega$ and every $s>0$,
--   $$
--    s\le\tau(\omega)\quad\Longrightarrow\quad H_1(\omega,s)=H_2(\omega,s).
--   $$
--   Then for every $t>0$, for $P$-almost every $\omega$ satisfying $t\le\tau(\omega)$,
--   $$
--   I_t[H_1](\omega)=I_t[H_2](\omega).
--   $$
--
--   This is the principal reuse theorem for replacing an integrand by an equivalent one on the portion of time before a stopping time.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_congr_of_le
--       (hτ : MeasureTheory.IsStoppingTime ℱ τ)
--       {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
--       (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
--       (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hm₂ : Measurable (Function.uncurry H₂))
--       (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
--       (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ τ ω → H₁ ω s = H₂ ω s)
--       {t : ℝ} (ht : 0 < t) :
--       ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
--         stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
--           = stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoLocality`](https://prove2.me/theorems/24c85544-31a3-4ffd-a08e-f5b9ac9b8eba).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`stochasticIntegralBrownian_congr_of_pos`](https://prove2.me/theorems/7c8a7f3d-a1b5-4c44-b668-4100f7891904), [`stochasticIntegralBrownian_stopped_eq_of_le`](https://prove2.me/theorems/dc8b0d30-1ce9-485a-bc89-a30aad33e6df).
--
--   Previous: [`stochasticIntegralBrownian_congr_of_pos`](https://prove2.me/theorems/7c8a7f3d-a1b5-4c44-b668-4100f7891904).
--
--   [Source excerpt, lines 566–580](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLocality.lean#L566-L580) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLocality.lean#L564-L600 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLocality`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le_readable
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ τ ω → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        = stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by sorry
