-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_compensator_add_sq_eq_readable
-- name    : LevyStochCalc.Brownian.Ito.compensator_add_sq_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:34.503432+00:00
-- url     : https://prove2.me/theorems/89a9fb44-6d50-4dd1-8c08-30019bcfbb53
-- title:
--   Quadratic Compensator Expansion for a Sum
-- statement:
--   This theorem gives the pointwise binomial expansion of the quadratic compensator for two bounded measurable integrands.
--
--   Let $H_1,H_2:\Omega\times\mathbb R\to\mathbb R$ be jointly measurable. Assume $C\ge0$ and $|H_1(\omega,s)|,|H_2(\omega,s)|\le C$. For every $t\in\mathbb R$ and $\omega\in\Omega$,
--
--   $$
--   \int_{[0,t]}(H_1+H_2)^2\,du
--   =\int_{[0,t]}H_1^2\,du
--   +2\int_{[0,t]}H_1H_2\,du
--   +\int_{[0,t]}H_2^2\,du.
--   $$
--
--   The integrals are with respect to Lebesgue measure, and the relevant boundedness and measurability hypotheses ensure integrability. This identity is used in polarization arguments for quadratic variation.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem compensator_add_sq_eq {t : ℝ} (ω : Ω) :
--       ∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u + H₂ ω u) ^ 2 ∂volume
--         = (∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u) ^ 2 ∂volume)
--           + 2 * (∫ u in Set.Icc (0 : ℝ) t, H₁ ω u * H₂ ω u ∂volume)
--           + ∫ u in Set.Icc (0 : ℝ) t, (H₂ ω u) ^ 2 ∂volume
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/PolarisedQuadVar`](https://prove2.me/theorems/00553e93-f879-4904-9333-b2c00471b79f).
--
--   Next: [`memLp_two_polarQuadVarIncrement`](https://prove2.me/theorems/e1f3d644-9e95-4545-bc1a-84c062eb6f44).
--
--   [Source excerpt, lines 85–89](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L85-L89) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L83-L119 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.PolarisedQuadVar`, declaration `LevyStochCalc.Brownian.Ito.compensator_add_sq_eq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/PolarisedQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)
include hC0 hCH₁ hCH₂ hm₁ hm₂

theorem LevyStochCalc.Brownian.Ito.compensator_add_sq_eq_readable {t : ℝ} (ω : Ω) :
    ∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u + H₂ ω u) ^ 2 ∂volume
      = (∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u) ^ 2 ∂volume)
        + 2 * (∫ u in Set.Icc (0 : ℝ) t, H₁ ω u * H₂ ω u ∂volume)
        + ∫ u in Set.Icc (0 : ℝ) t, (H₂ ω u) ^ 2 ∂volume := by sorry
