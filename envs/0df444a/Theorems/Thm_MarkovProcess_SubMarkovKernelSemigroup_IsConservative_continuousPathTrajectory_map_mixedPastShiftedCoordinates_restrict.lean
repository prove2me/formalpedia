-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_mixedPastShiftedCoordinates_restrict
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_mixedPastShiftedCoordinates_restrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:30.701916+00:00
-- url     : https://prove2.me/theorems/994a41c7-2daf-4093-9dcb-2bbf4dc4433a
-- title:
--   MarkovProcess: continuousPathTrajectory_map_mixedPastShiftedCoordinates_restrict
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_MixedFiniteMarginals_61bdbf42
import Definitions.Def_MarkovProcess_V3H_Restart_MixedPastFuture_e5e8ccdc
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
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
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite mixed past/future marginals of continuous trajectories

Every finite collection of rational coordinates drawn from the past through `S` and the shifted
future has the finite transition law on the corresponding union of absolute physical times,
followed by the canonical possibly noninjective coordinate pullback.  In particular, a terminal
past coordinate and a future coordinate at zero are both retained even though they observe the
same absolute time.

This is a finite-dimensional law identity.  The conditional factorization of that law through
the state at `S` is in `Restart/RationalRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]



end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite mixed past/future marginals of continuous trajectories

Every finite collection of rational coordinates drawn from the past through `S` and the shifted
future has the finite transition law on the corresponding union of absolute physical times,
followed by the canonical possibly noninjective coordinate pullback.  In particular, a terminal
past coordinate and a future coordinate at zero are both retained even though they observe the
same absolute time.

This is a finite-dimensional law identity.  The conditional factorization of that law through
the state at `S` is in `Restart/RationalRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory_map_mixedPastShiftedCoordinates_restrict
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (continuousPathTrajectory P hP default).map
        (I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S) =
      (finiteSetKernel P (MixedPastFuture.absolutePhysicalFinset S I)).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) := by sorry
