-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_pairing_char_joint_eq_zero
-- name    : LevyStochCalc.Driver.pairing_char_joint_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:37:43.270394+00:00
-- url     : https://prove2.me/theorems/6380e6e0-38fc-43a6-babf-fb1cdcbbc146
-- title:
--   pairing char joint eq zero
-- statement:
--   The source theorem `LevyStochCalc.Driver.pairing_char_joint_eq_zero` is extracted from `LevyStochCalc.Driver.JointComplement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointComplement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The orthogonal complement of the joint ranges

The times of a finite family of Brownian coordinate values, together with the horizon, sort into
an increasing grid whose last point is the horizon, and a finite family of window sets sits
inside a single window of finite mark intensity. A product of a Brownian cylinder character and a
window character is therefore a value character along the grid, and the joint grid induction
applies. The clamping horizon of that induction is strictly beyond the last grid point, so the
orthogonality hypothesis is carried up by the marked perp bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν] {T : ℝ}

section MarkSet

end MarkSet

section Complement

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

theorem _root_.LevyStochCalc.Driver.pairing_char_joint_eq_zero [Nonempty E] (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (F : Finset (Fin d × Set.Iic T))
    (G : Finset (Poisson.WindowSet E ν T)) (w : F → ℝ) (v : G → ℝ) :
    ∫ ω, Complex.exp (((∑ p : F, (W.W p.1.1).W (p.1.2 : ℝ) ω * w p : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((∑ B : G,
          (N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal * v B : ℝ) : ℂ)
        * Complex.I) * ((Z ω : ℝ) : ℂ) ∂P = 0 := by sorry
