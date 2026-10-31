-- Prove2me | Theorems.Thm_MarkovProcess_tendsto_integral_continuousPath_finiteDenseEvaluation_shift
-- name    : MarkovProcess.tendsto_integral_continuousPath_finiteDenseEvaluation_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:26:15.419561+00:00
-- url     : https://prove2.me/theorems/13e175da-9294-4564-8b05-b88f14cdd0de
-- title:
--   MarkovProcess: tendsto_integral_continuousPath_finiteDenseEvaluation_shift
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_ShiftCompactTestConvergence_fc2b2de1
import Definitions.Def_MarkovProcess_V3H_Trajectory_AllTimeFiniteMarginals_51403fc5
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dominated convergence for shifted continuous-path tests

This file records path-side dominated-convergence tools for deterministic times approached by
dense times. The measure is any finite measure on continuous-path space; no Markov or kernel
assumption is used.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]





end
end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dominated convergence for shifted continuous-path tests

This file records path-side dominated-convergence tools for deterministic times approached by
dense times. The measure is any finite measure on continuous-path space; no Markov or kernel
assumption is used.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]



open MarkovProcess in
omit [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] in

theorem MarkovProcess.tendsto_integral_continuousPath_finiteDenseEvaluation_shift
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (s : NNReal) (q : ℕ → DenseTime)
    (hq : Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds s))
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    Tendsto
      (fun n ↦ ∫ omega, f (fun j : J ↦
        omega (DenseTime.castOrderEmbedding (q n) +
          DenseTime.castOrderEmbedding j)) ∂mu)
      atTop
      (nhds (∫ omega, f (fun j : J ↦
        omega (s + DenseTime.castOrderEmbedding j)) ∂mu)) := by sorry
