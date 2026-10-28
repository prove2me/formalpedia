-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_compensator_sub_bounds_readable
-- name    : LevyStochCalc.Brownian.Ito.compensator_sub_bounds_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:28.933477+00:00
-- url     : https://prove2.me/theorems/5e8ee404-c1c1-469d-8d85-45ab11b64d10
-- title:
--   Bounds for a Compensator Increment
-- statement:
--   This theorem bounds the increment of the quadratic compensator of a bounded integrand.
--
--   Let $H:\Omega\times\mathbb R\to\mathbb R$ be jointly measurable, let $C\ge0$, and assume $|H(\omega,s)|\le C$. For $0\le a\le b$ and every $\omega\in\Omega$,
--
--   $$
--   0\le
--   \int_{[0,b]}H(\omega,u)^2\,du-\int_{[0,a]}H(\omega,u)^2\,du
--   \le C^2(b-a).
--   $$
--
--   The result identifies the compensator increment over $(a,b]$ with a nonnegative integral and bounds it using the interval length. It is a deterministic estimate for compensated quadratic-variation increments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem compensator_sub_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ω : Ω) :
--       0 ≤ (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
--             - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume
--         ∧ (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
--             - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume ≤ C ^ 2 * (b - a)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoQuadVarSum`](https://prove2.me/theorems/1add907f-537c-4a62-9c27-fe90c9b4a510).
--
--   Previous: [`condExp_quadVarIncrement`](https://prove2.me/theorems/cb7ab2d0-c60c-4b01-a336-abec1be3188b) · Next: [`memLp_two_sq_increment`](https://prove2.me/theorems/bdf6946b-1242-4316-90ea-7306d70caa0e).
--
--   [Source excerpt, lines 178–182](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoQuadVarSum.lean#L178-L182) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoQuadVarSum.lean#L176-L208 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoQuadVarSum`, declaration `LevyStochCalc.Brownian.Ito.compensator_sub_bounds`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoQuadVarSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hm hC0 hCH

theorem LevyStochCalc.Brownian.Ito.compensator_sub_bounds_readable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ω : Ω) :
    0 ≤ (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume
      ∧ (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume ≤ C ^ 2 * (b - a) := by sorry
