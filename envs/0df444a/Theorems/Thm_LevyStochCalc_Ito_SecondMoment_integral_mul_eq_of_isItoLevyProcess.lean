-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_SecondMoment_integral_mul_eq_of_isItoLevyProcess
-- name    : LevyStochCalc.Ito.SecondMoment.integral_mul_eq_of_isItoLevyProcess
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:46:51.826747+00:00
-- url     : https://prove2.me/theorems/7ce7cf52-aedb-4e95-a773-4a20b3ebe9dd
-- title:
--   integral mul eq of isItoLevyProcess
-- statement:
--   The source theorem `LevyStochCalc.Ito.SecondMoment.integral_mul_eq_of_isItoLevyProcess` is extracted from `LevyStochCalc.Ito.SecondMomentBilinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The bilinear second moment of two Itô–Lévy processes

For two Itô–Lévy processes `X` and `Y` over the same Lévy driver, with coefficients
`(X₀, b, σ, γ)` and `(Y₀, b', σ', γ')` satisfying the `L²` hypotheses, the expected product at a
time `T > 0` is

`𝔼[X_T Y_T] = 𝔼[X₀ Y₀] + ∫_0^T 𝔼[X_s b'_s + Y_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j σ'_j ds
  + 𝔼 ∫_0^T ∫_E γ γ' dν ds`,

the expectation form of the bilinear Itô formula, obtained from the polarised isometries of the
two stochastic integrals and the polarised drift identity. The drift term is the time integral of
the expected pairing; at every time the pairing is expanded along the decomposition, and the two
martingale pieces are read at the horizon by the martingale property.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Bilinear

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

theorem _root_.LevyStochCalc.Ito.SecondMoment.integral_mul_eq_of_isItoLevyProcess
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    {Y : ℝ → Ω → ℝ} {Y₀ : Ω → ℝ} {b' : ℝ → Ω → ℝ} {σ' : ℝ → Ω → Fin d → ℝ}
    {γ' : Ω → ℝ → E → ℝ}
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN Y Y₀ b' σ' γ')
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hY₀ : StronglyMeasurable[ℱ 0] Y₀) (hY₀2 : MemLp Y₀ 2 P)
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hb'p : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b' s ω)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, X T ω * Y T ω ∂P
      = ∫ ω, X₀ ω * Y₀ ω ∂P
        + (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b' s ω + Y s ω * b s ω ∂P)
        + (∑ j : Fin d, ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, σ s ω j * σ' s ω j ∂volume ∂P)
        + ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, γ ω s e * γ' ω s e ∂ν ∂volume ∂P := by sorry
