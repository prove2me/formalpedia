-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_isKolmogorovProcess_denseTimeTrajectory
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isKolmogorovProcess_denseTimeTrajectory
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:21:30.108328+00:00
-- url     : https://prove2.me/theorems/c1a818b6-fb93-43b2-8de5-71924d7ad577
-- title:
--   Kolmogorov property of the dense-time coordinate process
-- statement:
--   **The dense-time coordinate process is a Kolmogorov process, with the semigroup's own
--   constants.**  Under the intrinsic moment bound `HasKolmogorovMoments p q M`, the canonical
--   dense-time coordinate process of `P` started from any state satisfies the Kolmogorov increment
--   condition with exactly the exponents `p`, `q` and the constant `M` of that bound.  In particular
--   the estimate is uniform in the starting state.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/DenseTime/TwoPointMarginals.lean#L281-L310

import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KolmogorovMoments_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Kolmogorov
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Two-point marginals of the dense-time trajectory, and the intrinsic Kolmogorov bridge

The dense-time trajectory of a conservative sub-Markov kernel semigroup already has identified
one-time marginals.  This file identifies its two-time marginals: at dense times whose physical
images satisfy `iota d < iota d'`, the pair `(path d, path d')` has the law obtained by running
`P` for time `iota d` and then, from the state reached, for the increment `iota d' - iota d`.

The identification is then used to discharge the coordinate Kolmogorov hypothesis that every
trajectory theorem of the library assumes.  Under the intrinsic semigroup bound
`SubMarkovKernelSemigroup.HasKolmogorovMoments`, the canonical dense-time coordinate process is a
Kolmogorov process with a positive Hölder exponent below `(q - 1) / p`.

No continuity, modification, Markov-property, or path-regularity statement is proved here; only
the two-point law and the moment estimate it transports.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


noncomputable section











variable {A B C E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace E]







variable {D alpha : Type*} [MeasurableSpace alpha]






variable [StandardBorelSpace alpha] [Nonempty alpha]








variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [StandardBorelSpace alpha] [Nonempty alpha]

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isKolmogorovProcess_denseTimeTrajectory
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) (x : alpha) :
    IsKolmogorovProcess (fun r omega ↦ omega r)
      (denseTimeTrajectory P hP DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding x) p q M := by sorry
