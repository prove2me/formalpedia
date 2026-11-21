-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_itoFormula_between_gridStop_of_gridStopTrunc
-- name    : LevyStochCalc.Brownian.Ito.itoFormula_between_gridStop_of_gridStopTrunc
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:41:44.959663+00:00
-- url     : https://prove2.me/theorems/01cdf0a8-6462-4d44-a514-d0e57010a6a6
-- title:
--   itoFormula between gridStop of gridStopTrunc
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.itoFormula_between_gridStop_of_gridStopTrunc` is extracted from `LevyStochCalc.Ito.GridStopTruncated`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_GridStopTruncated_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The upward grid discretisation truncated at the horizon

The stopping time that stops at the first point of a uniform grid strictly beyond a stopping time
attains the horizon, so its values are not all grid points strictly below the horizon. Sending it
to `⊤` where it attains the horizon leaves a stopping time whose values are grid points strictly
below the horizon or `⊤`, and changes neither the horizon clipped at it nor an integrand cut off
at it on the closed window, hence neither the Itô integral at the horizon.

## Main statements

* `LevyStochCalc.Brownian.Ito.gridStopTrunc` — the upward grid discretisation of a stopping time,
  sent to `⊤` where it attains the horizon.
* `LevyStochCalc.Brownian.Ito.isStoppingTime_gridStopTrunc` — it is a stopping time.
* `LevyStochCalc.Brownian.Ito.gridStopTrunc_mono` — it is monotone in the stopping time.
* `LevyStochCalc.Brownian.Ito.measurableSpace_le_gridStopTrunc` — the σ-algebra of a stopping
  time is contained in that of its truncated grid discretisation.
* `LevyStochCalc.Brownian.Ito.gridStopTrunc_finiteRange` — its values are grid points strictly
  below the horizon, or `⊤`.
* `LevyStochCalc.Brownian.Ito.clipTime_gridStopTrunc` — the horizon clipped at it is the horizon
  clipped at the grid discretisation.
* `LevyStochCalc.Brownian.Ito.stopped_gridStopTrunc` — an integrand cut off at it agrees on the
  closed window with the integrand cut off at the grid discretisation.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le_horizon` — the Itô integral
  at a horizon depends on the integrand only on the window up to that horizon.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridStop_of_gridStopTrunc` — Itô's formula
  between the grid discretisations of two stopping times, from the identity between their
  truncations.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Truncate

variable {Ω : Type u}

end Truncate

section FiniteRange

variable {Ω : Type u}

end FiniteRange

section StoppingTime

variable {Ω : Type u} [MeasurableSpace Ω]

end StoppingTime

section Window

variable {Ω : Type u}

end Window

section Horizon

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Horizon

section GridShiftTransfer

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

theorem _root_.LevyStochCalc.Brownian.Ito.itoFormula_between_gridStop_of_gridStopTrunc
    {X : ℝ → Ω → Fin n → ℝ} {H : Fin n → Fin d → Ω → ℝ → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
    {σ τ : Ω → WithTop ℝ} {f : (Fin n → ℝ) → ℝ}
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    {c : Ω → Fin n → ℝ} {T : ℝ} (hT : 0 < T) (m : ℕ)
    (hmSt : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStopTrunc τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStopTrunc σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSt : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped (gridStopTrunc τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStopTrunc σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSt : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStopTrunc τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped (gridStopTrunc σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmSm : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStop τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStop σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSm : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped (gridStop τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStop σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSm : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped (gridStop σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hbase :
      (fun ω : Ω => f (X (clipTime (gridStopTrunc τ T m) T ω) ω + c ω)
          - f (X (clipTime (gridStopTrunc σ T m) T ω) ω + c ω))
        =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (gridStopTrunc τ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
              - Probability.stopped (gridStopTrunc σ T m)
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped (gridStopTrunc τ T m)
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                    - Probability.stopped (gridStopTrunc σ T m)
                        (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
                (hmSt p k) (hpSt p k) (hqSt p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped (gridStopTrunc τ T m)
                  (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped (gridStopTrunc σ T m)
                    (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                      * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume) :
    (fun ω : Ω => f (X (clipTime (gridStop τ T m) T ω) ω + c ω)
        - f (X (clipTime (gridStop σ T m) T ω) ω + c ω))
      =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped (gridStop τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped (gridStop σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped (gridStop τ T m)
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped (gridStop σ T m)
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
              (hmSm p k) (hpSm p k) (hqSm p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (gridStop τ T m)
                (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped (gridStop σ T m)
                  (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by sorry
