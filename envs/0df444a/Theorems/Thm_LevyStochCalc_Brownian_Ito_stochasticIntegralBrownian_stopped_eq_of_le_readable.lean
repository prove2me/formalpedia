-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_stopped_eq_of_le_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:08.671226+00:00
-- url     : https://prove2.me/theorems/dc8b0d30-1ce9-485a-bc89-a30aad33e6df
-- title:
--   Locality of the Itô Integral at an Unreached Stopping Time
-- statement:
--   This proves the local property of the Itô integral.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, let $\tau$ be an $\mathcal F$-stopping time, and let $W$ be a Brownian motion with Brownian filtration $\mathcal F$. Let $H$ be jointly measurable and progressively measurable, and assume that for every $T>0$ its `ENNReal` energy is finite:
--   $$
--   \int_\Omega\int_{[0,T]}\|H(\omega,s)\|_+^2\,ds\,dP<\top.
--   $$
--   For every $t>0$, for $P$-almost every $\omega$ such that $t\le\tau(\omega)$, the integral of the stopped integrand agrees with the original integral:
--   $$
--   I_t[\operatorname{stopped}(\tau,H)](\omega)=I_t[H](\omega).
--   $$
--
--   The conclusion is conditional on the event that the stopping time has not been reached by time $t$; the equality is not asserted outside that event.
--
--   **Formalization Note.** The stopping-time values and the comparison with $t$ use `WithTop ℝ`; all finite-energy conditions are strict inequalities below $\top$ in `ENNReal`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_stopped_eq_of_le
--       (hτ : MeasureTheory.IsStoppingTime ℱ τ)
--       {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
--       (hp : Probability.ProgressivelyMeasurable ℱ H)
--       (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {t : ℝ} (ht : 0 < t) :
--       ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
--         stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H)
--             (Probability.measurable_uncurry_stopped hτ hm)
--             (Probability.ProgressivelyMeasurable.stopped hτ hp)
--             (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H ω s) hq) t ω
--           = stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoLocality`](https://prove2.me/theorems/24c85544-31a3-4ffd-a08e-f5b9ac9b8eba).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Probability/StoppedProgressive`](https://prove2.me/theorems/602d883b-27f9-43ed-bb5c-77dd184db556), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/ItoOptionalStopping`](https://prove2.me/theorems/1d25c358-1966-4cac-ba37-96d7bf5aaf7d).
--
--   Supporting theorems: [`eventually_gridStop_lt`](https://prove2.me/theorems/e741dfe5-2d5c-477d-97d6-46f4687f6103), [`gridStopAux_le_iff`](https://prove2.me/theorems/6f0d962f-df1d-4b16-a483-6c727c1385c0), [`stochasticIntegralBrownian_stopped`](https://prove2.me/theorems/ed4209dc-2e3a-4843-8705-dade9e7c1cbc).
--
--   Previous: [`eventually_gridStop_lt`](https://prove2.me/theorems/e741dfe5-2d5c-477d-97d6-46f4687f6103) · Next: [`stochasticIntegralBrownian_congr_of_pos`](https://prove2.me/theorems/7c8a7f3d-a1b5-4c44-b668-4100f7891904).
--
--   [Source excerpt, lines 294–306](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLocality.lean#L294-L306) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLocality.lean#L291-L500 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLocality`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
include hℱ

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le_readable
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H)
          (Probability.measurable_uncurry_stopped hτ hm)
          (Probability.ProgressivelyMeasurable.stopped hτ hp)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H ω s) hq) t ω
        = stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω := by sorry
