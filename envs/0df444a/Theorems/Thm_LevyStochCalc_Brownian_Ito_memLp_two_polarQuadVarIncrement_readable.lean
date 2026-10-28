-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_memLp_two_polarQuadVarIncrement_readable
-- name    : LevyStochCalc.Brownian.Ito.memLp_two_polarQuadVarIncrement_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:58.172231+00:00
-- url     : https://prove2.me/theorems/e1f3d644-9e95-4545-bc1a-84c062eb6f44
-- title:
--   L² Membership of Polarized Compensated Increments
-- statement:
--   Let $H_1,H_2$ satisfy the stated measurability, progressive-measurability, joint square-integrability, and uniform bound assumptions, including the corresponding assumptions for $H_1+H_2$. If $C\ge0$ and $0\le a<b$, then
--
--   $$\mathrm{polarQuadVarIncrement}_{a,b}(H_1,H_2)\in L^2(P).$$
--
--   Thus the compensated product of the two Itô-integral increments has `MemLp` exponent $2$ under $P$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem memLp_two_polarQuadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       MemLp (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b) 2 P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/PolarisedQuadVar`](https://prove2.me/theorems/00553e93-f879-4904-9333-b2c00471b79f).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`compensator_add_sq_eq`](https://prove2.me/theorems/89a9fb44-6d50-4dd1-8c08-30019bcfbb53), [`compensator_sub_bounds`](https://prove2.me/theorems/5e8ee404-c1c1-469d-8d85-45ab11b64d10), [`memLp_two_sq_increment`](https://prove2.me/theorems/bdf6946b-1242-4316-90ea-7306d70caa0e), [`stochasticIntegralBrownian_add`](https://prove2.me/theorems/63f87c77-88d3-49b3-b12f-0856c509d6a6).
--
--   Previous: [`compensator_add_sq_eq`](https://prove2.me/theorems/89a9fb44-6d50-4dd1-8c08-30019bcfbb53) · Next: [`condExp_polarQuadVarIncrement`](https://prove2.me/theorems/90ba8838-f516-4c4a-a54e-03f7270ecbb4).
--
--   [Source excerpt, lines 142–143](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L142-L143) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/PolarisedQuadVar.lean#L140-L167 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.PolarisedQuadVar`, declaration `LevyStochCalc.Brownian.Ito.memLp_two_polarQuadVarIncrement`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
include hℱ hma hpa hqa hC0 hCH₁ hCH₂

theorem LevyStochCalc.Brownian.Ito.memLp_two_polarQuadVarIncrement_readable {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b) 2 P := by sorry
