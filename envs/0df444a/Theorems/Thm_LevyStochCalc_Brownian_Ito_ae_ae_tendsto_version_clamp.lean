-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_ae_tendsto_version_clamp
-- name    : LevyStochCalc.Brownian.Ito.ae_ae_tendsto_version_clamp
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:38:18.906798+00:00
-- url     : https://prove2.me/theorems/13a93629-6911-4010-aa5d-2841f31ebf0d
-- title:
--   ae ae tendsto version clamp
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.ae_ae_tendsto_version_clamp` is extracted from `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.Brownian.Ito.ae_ae_tendsto_version_clamp
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Xj : ℕ → ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
    (hXj : ∀ j : ℕ, IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
      X₀ (clampDrift b j) (Xj j))
    {T : ℝ} {ns : ℕ → ℕ}
    (hns : ∀ i : ℕ, clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω)) := by sorry
