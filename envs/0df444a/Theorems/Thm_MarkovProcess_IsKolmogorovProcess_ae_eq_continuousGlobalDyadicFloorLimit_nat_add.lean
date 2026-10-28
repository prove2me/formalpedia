-- Prove2me | Theorems.Thm_MarkovProcess_IsKolmogorovProcess_ae_eq_continuousGlobalDyadicFloorLimit_nat_add
-- name    : MarkovProcess.IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit_nat_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:20:27.70527+00:00
-- url     : https://prove2.me/theorems/01f347ec-c2f9-40fa-857e-4207b345e6bb
-- title:
--   Global dyadic floor limit modifies rational-time samples
-- statement:
--   At a fixed rational time written as a natural shift plus a local time in `[0,1]`, the
--   globally totalized continuous path is a modification of the original process.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/GlobalDyadicFloorModification.lean#L188-L222

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.LocallyFinite
open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A global continuous modification assembled from canonical unit paths

The nonnegative real half-line is covered by the closed unit intervals `[n, n + 1]`.  On each
piece we use the canonical dyadic-floor limit of the process shifted by `n`.  Exact endpoint
identities make these pieces compatible, so `Set.liftCover` gives an honest raw global path.
On the simultaneous probability-one event where every canonical unit piece is continuous, local
finiteness of the closed cover makes the raw path continuous.  A single constant global fallback
then gives a total path which is continuous for every sample.

No measurability of the path-valued map, path-space law, Markov property, or Hunt-process claim is
asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem MarkovProcess.IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit_nat_add
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) (n : ℕ) (t : NNRat) (ht : t ≤ 1) :
    X (n + t) =ᵐ[P] fun ω ↦
      continuousGlobalDyadicFloorLimit X ω (↑((n : NNRat) + t) : ℝ≥0) := by sorry
