-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_ae_eq_zero_of_perp_joint
-- name    : LevyStochCalc.Driver.ae_eq_zero_of_perp_joint
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:02:08.343267+00:00
-- url     : https://prove2.me/theorems/722bafa6-1ccb-4a1d-9d69-396009b3c816
-- title:
--   ae eq zero of perp joint
-- statement:
--   The source theorem `LevyStochCalc.Driver.ae_eq_zero_of_perp_joint` is extracted from `LevyStochCalc.Driver.JointComplement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPBrownian_F000
import Definitions.Def_LevyStochCalc_Driver_JointCharacters_F000
import Definitions.Def_LevyStochCalc_Driver_JointFiltration_F000
import Definitions.Def_LevyStochCalc_Driver_JointMultidim_F000
import Definitions.Def_LevyStochCalc_Poisson_PerpBridge_F000

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

theorem _root_.LevyStochCalc.Driver.ae_eq_zero_of_perp_joint [Nonempty E] (D : LevyDriver P d ν) (hd : 0 < d) (hT : 0 < T)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hperp : ∀ i, PerpItoIntegrals (D.W.W i) (Brownian.augFiltration D.filtration P)
      (D.isBrownianFiltration_aug i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T,
      ∫ ω, Z ω * G'.integral D.N D.isPoissonFiltration_aug ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    Z =ᵐ[P] 0 := by sorry
