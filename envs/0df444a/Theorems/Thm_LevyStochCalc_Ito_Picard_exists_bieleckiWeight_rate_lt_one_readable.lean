-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_exists_bieleckiWeight_rate_lt_one_readable
-- name    : LevyStochCalc.Ito.Picard.exists_bieleckiWeight_rate_lt_one_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:37.94121+00:00
-- url     : https://prove2.me/theorems/2424b633-168d-49a1-be31-197cd8b56a43
-- title:
--   Existence of a Bielecki Weight with Contraction Rate Below One
-- statement:
--   This asserts that a sufficiently large positive Bielecki weight makes the displayed contraction factor strictly less than one.
--
--   For natural dimensions $n,d$, a horizon $T>0$, and a real constant $L$, there exists $\beta>0$ such that
--
--   $$\left(\operatorname{ofReal}\left(\frac{3\bigl(nL^2T+n\,dL^2+nL^2\bigr)}{2\beta}\right)\right)^{1/2}<1.$$
--
--   Here `ENNReal.ofReal` produces an $[0,\infty]$ value and the exponent is the real power $1/2$. This supplies the weight required for a strict Picard contraction.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_bieleckiWeight_rate_lt_one (L : ℝ) (hT : 0 < T) :
--       ∃ β : ℝ, 0 < β ∧
--         (ENNReal.ofReal
--           ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
--             / (2 * β))) ^ ((1 : ℝ) / 2) < 1
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardContractionEstimate`](https://prove2.me/theorems/8cad574e-6914-4d17-98ca-b6df8ebe8b41).
--
--   Next: [`bieleckiNorm_picardStepOnStop_sub_rawStop_le`](https://prove2.me/theorems/f7bce8db-81a1-4513-838e-14d438224f96).
--
--   [Source excerpt, lines 344–348](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardContractionEstimate.lean#L344-L348) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardContractionEstimate.lean#L342-L362 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardContractionEstimate`, declaration `LevyStochCalc.Ito.Picard.exists_bieleckiWeight_rate_lt_one`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContractionEstimate

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardContractionEstimate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg

theorem LevyStochCalc.Ito.Picard.exists_bieleckiWeight_rate_lt_one_readable (L : ℝ) (hT : 0 < T) :
    ∃ β : ℝ, 0 < β ∧
      (ENNReal.ofReal
        ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
          / (2 * β))) ^ ((1 : ℝ) / 2) < 1 := by sorry
