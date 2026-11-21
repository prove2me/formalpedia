-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_norm_clampProcess_sub_le
-- name    : LevyStochCalc.Brownian.Ito.lintegral_sq_norm_clampProcess_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:36:15.193689+00:00
-- url     : https://prove2.me/theorems/5e2e04e6-842b-4d04-807f-8bead0356a0b
-- title:
--   lintegral sq norm clampProcess sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_norm_clampProcess_sub_le` is extracted from `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F000

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

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_sq_norm_clampProcess_sub_le
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k))
    (hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (j : ℕ) {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫⁻ ω, (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
            X₀ (clampDrift b j) t ω
        - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ clampMesh P H b T j := by sorry
