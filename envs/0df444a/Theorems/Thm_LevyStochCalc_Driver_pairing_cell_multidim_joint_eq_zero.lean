-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_pairing_cell_multidim_joint_eq_zero
-- name    : LevyStochCalc.Driver.pairing_cell_multidim_joint_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:53:39.021828+00:00
-- url     : https://prove2.me/theorems/597dc94a-e956-4acc-8c95-c2ac84afed81
-- title:
--   pairing cell multidim joint eq zero
-- statement:
--   The source theorem `LevyStochCalc.Driver.pairing_cell_multidim_joint_eq_zero` is extracted from `LevyStochCalc.Driver.JointMultidim`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPMultidim_F000
import Definitions.Def_LevyStochCalc_Driver_JointGrid_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mixed cell lemma for a multidimensional Brownian motion

A character of a vector of Brownian increments across a cell is the character of the increment
of a unit combination, scaled by the length of the weight vector, so the mixed cell lemma for a
single Brownian motion carries over to the multidimensional driver with the Poisson character
riding along unchanged.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Cell

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

theorem _root_.LevyStochCalc.Driver.pairing_cell_multidim_joint_eq_zero (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℂ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, ‖V ω‖ ≤ Mv) (hZV : ∫ ω, ((Z ω : ℝ) : ℂ) * V ω ∂P = 0) (lam : Fin d → ℝ) :
    ∫ ω, ((Z ω : ℝ) : ℂ) * V ω
      * (Complex.exp (Complex.I
          * ((∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω) : ℝ) : ℂ))
        * charAt N w Bfam b ω) ∂P = 0 := by sorry
