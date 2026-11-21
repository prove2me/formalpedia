-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_seq_ae_tendsto_of_tendsto_lintegral
-- name    : LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:48:47.471919+00:00
-- url     : https://prove2.me/theorems/cefc965c-f547-45ab-b0fd-5f7279a387f7
-- title:
--   exists seq ae tendsto of tendsto lintegral
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral` is extracted from `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Coefficients of a vector Itô process clamped at a finite level

Clamping the coefficients of a vector Itô process at level `j` leaves bounded coefficients of
finite energy whose distance in energy to the original coefficients tends to `0`, and the process
they drive stays within that distance of the original one in `L²`, uniformly on a bounded window;
along a suitable subsequence of levels the clamped processes converge to the original one almost
surely.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampCoeff`, `clampDrift` — the clamped coefficients.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp` — the mesh of the approximation.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section ClampProcess

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} [Finite ι] {u : ℕ → ι → α → ℝ} {v : ι → α → ℝ}
    (hu : ∀ (i : ℕ) (c : ι), Measurable (u i c)) (hv : ∀ c : ι, Measurable (v c))
    (h : ∀ c : ι, Filter.Tendsto (fun i : ℕ => ∫⁻ a, (‖u i c a - v c a‖₊ : ℝ≥0∞) ^ 2 ∂μ)
      Filter.atTop (𝓝 0)) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧
      ∀ᵐ a ∂μ, ∀ c : ι, Filter.Tendsto (fun i : ℕ => u (ms i) c a) Filter.atTop (𝓝 (v c a)) := by sorry
