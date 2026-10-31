-- Prove2me | Theorems.Thm_MarkovProcess_continuous_continuousShiftedUnitDyadicFloorLimit
-- name    : MarkovProcess.continuous_continuousShiftedUnitDyadicFloorLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:38.846579+00:00
-- url     : https://prove2.me/theorems/446f888a-1eb8-490b-8750-f8c42aa6977f
-- title:
--   MarkovProcess: continuous_continuousShiftedUnitDyadicFloorLimit
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicFloor_a02de258
import Definitions.Def_MarkovProcess_V3H_Continuity_KolmogorovTimeShift_b20f4218
import Definitions.Def_MarkovProcess_V3H_Continuity_ShiftedUnitModification_dfb22f1c
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous modifications on shifted unit intervals

This file applies the unit-interval totalization to a nonnegative-rational time shift.  It also
identifies the endpoints of the underlying canonical limit exactly, for every sample, using the
eventual constancy of dyadic approximations at dyadic grid times.

No global path is glued here, and no path-space measurability, law, or Hunt-process property is
asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]













end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous modifications on shifted unit intervals

This file applies the unit-interval totalization to a nonnegative-rational time shift.  It also
identifies the endpoints of the underlying canonical limit exactly, for every sample, using the
eventual constancy of dyadic approximations at dyadic grid times.

No global path is glued here, and no path-space measurability, law, or Hunt-process property is
asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal



variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]



open MarkovProcess in
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in

theorem MarkovProcess.continuous_continuousShiftedUnitDyadicFloorLimit
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    Continuous (continuousShiftedUnitDyadicFloorLimit k X ω) := by sorry
