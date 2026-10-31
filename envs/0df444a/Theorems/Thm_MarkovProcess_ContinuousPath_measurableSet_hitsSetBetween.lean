-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_measurableSet_hitsSetBetween
-- name    : MarkovProcess.ContinuousPath.measurableSet_hitsSetBetween
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:38.645523+00:00
-- url     : https://prove2.me/theorems/245f2fca-f39f-470b-a225-bbfe5512e8a3
-- title:
--   MarkovProcess: measurableSet_hitsSetBetween
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_ClosedSetDetection_642089d8
import Definitions.Def_MarkovProcess_V3H_Path_RelativeHitting_d5970fdd
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Closed-set detection after a stopping time

This file relativizes closed-set detection to the random compact interval between a stopping
time and a fixed deterministic horizon.  The lower endpoint is truncated at the horizon, so it
is a bounded finite stopping time.  Continuity reduces detection on that interval to its two
endpoints and the fixed enumeration of nonnegative rational times strictly between them.

Public declarations:

* `ContinuousPath.hitsSetBetween`;
* `ContinuousPath.measurableSet_hitsSetBetween`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]





variable [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]



end ContinuousPath

end

end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Closed-set detection after a stopping time

This file relativizes closed-set detection to the random compact interval between a stopping
time and a fixed deterministic horizon.  The lower endpoint is truncated at the horizon, so it
is a bounded finite stopping time.  Continuity reduces detection on that interval to its two
endpoints and the fixed enumeration of nonnegative rational times strictly between them.

Public declarations:

* `ContinuousPath.hitsSetBetween`;
* `ContinuousPath.measurableSet_hitsSetBetween`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal




variable {alpha : Type*} [PseudoMetricSpace alpha]





variable [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.measurableSet_hitsSetBetween
    (T : ContinuousPath alpha → ℝ≥0∞)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha)) T)
    (t : NNReal) (F : Set alpha) (hF : IsClosed F) :
    MeasurableSet[canonicalFiltration (alpha := alpha) t] (hitsSetBetween T t F) := by sorry
