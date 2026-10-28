-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_indicator_Ioc_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:19.62392+00:00
-- url     : https://prove2.me/theorems/bcc8c011-e83f-4b9e-a0e6-5de008451e39
-- title:
--   Locality on a Half-Open Time Interval
-- statement:
--   Let $W$ be a Brownian motion with Brownian filtration, let $H:Ω×ℝ→ℝ$ be jointly measurable and progressively measurable with finite squared `ENNReal` energy on every positive interval, and let $0≤a<b$. Assume the restricted integrand $\mathbf{1}_{(a,b]}(s)H(ω,s)$ is jointly measurable, progressively measurable, and has finite squared energy on every positive interval. Then, for every $t>0$,
--
--   $$\int_0^t\mathbf{1}_{(a,b]}(s)H_s\,dW_s
--   =\int_0^{\min(b,t)}H_s\,dW_s-\int_0^{\min(a,t)}H_s\,dW_s\quad P\text{-almost everywhere}.$$
--
--   The indicator is the `Set.Ioc a b` indicator, so the interval is $(a,b]$. This is the locality and increment formula for the `L²` Brownian Itô integral.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_indicator_Ioc
--       {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
--       (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
--       (hp : Probability.ProgressivelyMeasurable ℱ H)
--       (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
--       (him : Measurable (Function.uncurry fun ω s =>
--         (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s))
--       (hip : Probability.ProgressivelyMeasurable ℱ fun ω s =>
--         (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
--       (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {t : ℝ} (ht : 0 < t) :
--       stochasticIntegralBrownian W ℱ hℱ
--           (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) him hip hiq t
--         =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min b t) ω
--           - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min a t) ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraAssociativity`](https://prove2.me/theorems/738b1003-832c-420c-a910-2008630209bc).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`stepIoc_eval`](https://prove2.me/theorems/229a87fb-276d-451b-880f-3ee228acc687), [`stepIoc₀_eval`](https://prove2.me/theorems/2c0d5744-8278-417f-9f9c-dd287d9c0a4f), [`stochasticIntegralBrownian_integralAgainst`](https://prove2.me/theorems/ad605701-48f4-400c-83de-f35b5212c9ce).
--
--   Previous: [`stepIoc₀_eval`](https://prove2.me/theorems/2c0d5744-8278-417f-9f9c-dd287d9c0a4f).
--
--   [Source excerpt, lines 388–406](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean#L388-L406) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraAssociativity`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean, lines 386-445). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc_readable
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (him : Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s))
    (hip : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) him hip hiq t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min b t) ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min a t) ω := by sorry
