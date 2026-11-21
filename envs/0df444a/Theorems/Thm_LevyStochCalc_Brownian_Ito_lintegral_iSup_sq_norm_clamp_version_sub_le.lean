-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_iSup_sq_norm_clamp_version_sub_le
-- name    : LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_clamp_version_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:09:23.180108+00:00
-- url     : https://prove2.me/theorems/d7b7beef-feeb-4e6c-b0a2-6627ed7739cd
-- title:
--   lintegral iSup sq norm clamp version sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_clamp_version_sub_le` is extracted from `LevyStochCalc.Ito.VectorItoVersionUnbounded`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F001
import Definitions.Def_LevyStochCalc_Ito_VectorItoVersionSup_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Continuous versions for unbounded coefficients

Clamping the coefficients at level `j` gives a vector Itô process with bounded coefficients, hence
a continuous version. The window supremum of the difference of two such versions is controlled by
the clamping mesh, so along levels whose meshes are summable the versions converge uniformly on
each window.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_clamp_version_sub_le` — the window supremum
  of the difference of two clamped versions, in terms of the clamping mesh.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal

universe u

section ClampSup

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

include hcoord in

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_clamp_version_sub_le
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
    {X₀ : Ω → Fin n → ℝ} {b : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {j j' : ℕ} {Xj Xj' : ℝ → Ω → Fin n → ℝ}
    (hXj : IsVectorItoVersion W ℱ hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
      X₀ (clampDrift b j) Xj)
    (hXj' : IsVectorItoVersion W ℱ hcoord (clampCoeff H j')
      (fun p k => measurable_clampCoeff hm j' p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j' p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j' p k T' hT')
      X₀ (clampDrift b j') Xj')
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Xj' (t : ℝ) ω - Xj (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 32 * (n : ℝ≥0∞) ^ 2 * (clampMesh P H b T j + clampMesh P H b T j') := by sorry
