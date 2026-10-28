-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_stopped_readable
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:37.341016+00:00
-- url     : https://prove2.me/theorems/ed4209dc-2e3a-4843-8705-dade9e7c1cbc
-- title:
--   Finite-Range Optional Stopping Identity
-- statement:
--   This proves optional stopping for a stopping time whose values below the horizon form a finite set.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, let $\tau:\Omega\to\operatorname{WithTop}(\mathbb R)$ be an $\mathcal F$-stopping time, and let $W$ and $\mathcal F$ form a Brownian motion and Brownian filtration. Let $H$ be jointly measurable and progressively measurable, with
--   $$
--   \int_\Omega\int_{[0,T]}\|H(\omega,s)\|_+^2\,ds\,dP<\top
--   $$
--   for every $T>0$. Fix $t>0$ and a finite set $J\subset\mathbb R$ such that every $c\in J$ satisfies $0\le c$ and $c<t$, and assume that for every $\omega$ either $\tau(\omega)=c$ for some $c\in J$ or $t\le\tau(\omega)$.
--
--   Then, $P$-almost everywhere,
--   $$
--   I_t[\operatorname{stopped}(\tau,H)](\omega)
--   =
--   I_t[H](\omega)
--   -\sum_{c\in J}\operatorname{hitInd}(\tau,c,\omega)\bigl(I_t[H](\omega)-I_c[H](\omega)\bigr).
--   $$
--
--   The stopped integrand is equipped with the measurability, progressive-measurability, and finite-energy witnesses generated from the hypotheses.
--
--   This is the finite-range identity from which the general local property is obtained by approximation.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stochasticIntegralBrownian_stopped
--       (hτ : MeasureTheory.IsStoppingTime ℱ τ)
--       {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
--       (hp : Probability.ProgressivelyMeasurable ℱ H)
--       (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {t : ℝ} (ht : 0 < t) (J : Finset ℝ)
--       (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
--       (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
--       stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H)
--           (Probability.measurable_uncurry_stopped hτ hm)
--           (Probability.ProgressivelyMeasurable.stopped hτ hp)
--           (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H ω s) hq) t
--         =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
--           - ∑ c ∈ J, hitInd τ c ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
--               - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoOptionalStopping`](https://prove2.me/theorems/1d25c358-1966-4cac-ba37-96d7bf5aaf7d).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Probability/StoppedProgressive`](https://prove2.me/theorems/602d883b-27f9-43ed-bb5c-77dd184db556), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Selected supporting theorems: [`exists_stochasticIntegralBrownian_finsetSum`](https://prove2.me/theorems/b0d141d4-c156-4326-80cf-9bf508518511), [`lintegral_energy_lt_top_of_bound`](https://prove2.me/theorems/16b799ee-a736-423f-b93d-da4952047315), [`mul_stochasticIntegralBrownian_indIoc`](https://prove2.me/theorems/13bdf081-9a6f-4dc1-a40f-ce4f657ba4ff), [`progressivelyMeasurable_mul_indIoc`](https://prove2.me/theorems/030165f7-acc3-4866-b777-afeba0e9b4de), [`stochasticIntegralBrownian_indicator_Ioc`](https://prove2.me/theorems/bcc8c011-e83f-4b9e-a0e6-5de008451e39).
--
--   Previous: [`stopped_eq_sub_sum`](https://prove2.me/theorems/ca6db2c8-b052-412e-99f9-f5b6637e3786).
--
--   [Source excerpt, lines 240–255](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoOptionalStopping.lean#L240-L255) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoOptionalStopping.lean#L238-L334 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoOptionalStopping`, declaration `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoOptionalStopping

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoOptionalStopping.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
variable (τ : Ω → WithTop ℝ)
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ

theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_readable
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H)
        (Probability.measurable_uncurry_stopped hτ hm)
        (Probability.ProgressivelyMeasurable.stopped hτ hp)
        (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H ω s) hq) t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
        - ∑ c ∈ J, hitInd τ c ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω) := by sorry
