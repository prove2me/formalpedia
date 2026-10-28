-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_stochasticIntegralBrownian_finsetSum_readable
-- name    : LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:21.939609+00:00
-- url     : https://prove2.me/theorems/b0d141d4-c156-4326-80cf-9bf508518511
-- title:
--   Finite-Sum Linearity of the Brownian Itô Integral
-- statement:
--   This statement gives finite-sum linearity of the Brownian Itô integral together with admissibility data for the summed integrand. Let $(Ω,P)$ be a probability space, let $W$ be a Brownian motion, and let $ℱ$ be a Brownian filtration. For an index type $ι$, let $H_i:Ω×ℝ→ℝ$ be jointly measurable and progressively measurable for every $i∈ι$, and assume that each $H_i$ has finite squared `ENNReal` energy on every interval $[0,T]$ with $T>0$. Let $J$ be a finite subset of $ι$ and let $T>0$.
--
--   There exist joint measurability and progressive-measurability proofs for the finite sum $\sum_{i∈J}H_i$, together with the corresponding finite-energy property, such that
--
--   $$\int \left(\sum_{i∈J}H_i\right)dW=\sum_{i∈J}\int H_i\,dW\quad P\text{-almost everywhere at time }T.$$
--
--   The theorem is existential in the auxiliary admissibility proofs; it does not assert uniqueness of those proofs. It packages finite-sum linearity for later constructions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_stochasticIntegralBrownian_finsetSum {ι : Type*}
--       (H : ι → Ω → ℝ → ℝ) (hm : ∀ i, Measurable (Function.uncurry (H i)))
--       (hp : ∀ i, Probability.ProgressivelyMeasurable ℱ (H i))
--       (hq : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (J : Finset ι) {T : ℝ} (hT : 0 < T) :
--       ∃ (hms : Measurable (Function.uncurry fun ω u => ∑ i ∈ J, H i ω u))
--         (hps : Probability.ProgressivelyMeasurable ℱ fun ω u => ∑ i ∈ J, H i ω u)
--         (hqs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
--           (‖∑ i ∈ J, H i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
--         stochasticIntegralBrownian W ℱ hℱ (fun ω u => ∑ i ∈ J, H i ω u) hms hps hqs T
--           =ᵐ[P] fun ω => ∑ i ∈ J,
--             stochasticIntegralBrownian W ℱ hℱ (H i) (hm i) (hp i) (hq i) T ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFinsetSum`](https://prove2.me/theorems/3c65a1ac-837e-48a1-b323-dc87feeb6397).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`lintegral_energy_lt_top_of_bound`](https://prove2.me/theorems/16b799ee-a736-423f-b93d-da4952047315), [`stochasticIntegralBrownian_add`](https://prove2.me/theorems/63f87c77-88d3-49b3-b12f-0856c509d6a6), [`stochasticIntegralBrownian_ae_zero`](https://prove2.me/theorems/57111c52-f9fc-4a29-b5e6-79796fbc45a3).
--
--   Previous: [`stochasticIntegralBrownian_sub`](https://prove2.me/theorems/a954497d-231b-4ebc-910f-e11817f51410).
--
--   [Source excerpt, lines 124–136](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFinsetSum.lean#L124-L136) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFinsetSum.lean#L122-L177 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFinsetSum`, declaration `LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum_readable {ι : Type*}
    (H : ι → Ω → ℝ → ℝ) (hm : ∀ i, Measurable (Function.uncurry (H i)))
    (hp : ∀ i, Probability.ProgressivelyMeasurable ℱ (H i))
    (hq : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (J : Finset ι) {T : ℝ} (hT : 0 < T) :
    ∃ (hms : Measurable (Function.uncurry fun ω u => ∑ i ∈ J, H i ω u))
      (hps : Probability.ProgressivelyMeasurable ℱ fun ω u => ∑ i ∈ J, H i ω u)
      (hqs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
        (‖∑ i ∈ J, H i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      stochasticIntegralBrownian W ℱ hℱ (fun ω u => ∑ i ∈ J, H i ω u) hms hps hqs T
        =ᵐ[P] fun ω => ∑ i ∈ J,
          stochasticIntegralBrownian W ℱ hℱ (H i) (hm i) (hp i) (hq i) T ω := by sorry
