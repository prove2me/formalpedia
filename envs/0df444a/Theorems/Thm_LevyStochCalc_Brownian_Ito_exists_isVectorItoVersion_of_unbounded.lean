-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_isVectorItoVersion_of_unbounded
-- name    : LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:52:02.943296+00:00
-- url     : https://prove2.me/theorems/8ce029bf-840b-4eca-b9ef-4a0c3f6daca6
-- title:
--   exists isVectorItoVersion of unbounded
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded` is extracted from `LevyStochCalc.Ito.VectorItoVersionLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002
import Definitions.Def_LevyStochCalc_Ito_VectorItoVersionLimit_F000
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Continuous versions of vector Itô processes with unbounded coefficients

Clamping the coefficients at a level whose mesh decays geometrically on every bounded window
produces versions whose window suprema of consecutive differences are summable almost surely,
hence converge uniformly on compact time sets; the limit is a continuous adapted version of the
vector Itô process driven by the unclamped coefficients.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampMesh_mono_window` — the clamping mesh grows with the window.
* `LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_window_lt` — clamping levels along which the
  mesh of every window decays geometrically.
* `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded` — a continuous adapted
  version of a vector Itô process whose coefficients have finite energy on every window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal Topology

universe u

section Elementary

end Elementary

section Mesh

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

end Mesh

section Limit

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

theorem _root_.LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded
    (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p))
    (hbq : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X := by sorry
