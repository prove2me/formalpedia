-- Prove2me | Theorems.Thm_MarkovProcess_continuousProcess_driftSemigroup_eq
-- name    : MarkovProcess.continuousProcess_driftSemigroup_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:15.878832+00:00
-- url     : https://prove2.me/theorems/5f060f4e-d30a-40d7-a2cd-2732ecda4f90
-- title:
--   MarkovProcess: continuousProcess_driftSemigroup_eq
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Examples_Drift_f1e2d4e2
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
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
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The deterministic drift semigroup and its continuous-path process

On a finite-dimensional real normed space the transition semigroup that translates by `t • v` in
time `t` is a conservative Feller semigroup satisfying the Kolmogorov moment criterion with
exponents `p = q = 2` and constant `‖v‖²`.  The existence-and-uniqueness theorem of
`MarkovProcess.Main` therefore applies, and the process it produces is identified: from every
starting point `x` its law is the Dirac mass at the straight line `t ↦ x + t • v`.

Together with `MarkovProcess.Examples.Identity` this shows that the hypotheses of the main
theorem are satisfiable by a semigroup that genuinely moves.  Nothing here is claimed about a
semigroup with a nonzero diffusion part; for that see `MarkovProcess.Examples.HeatSemigroup`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Definition









end Definition

section Feller











end Feller

section Moments



end Moments

section Process













end Process

end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The deterministic drift semigroup and its continuous-path process

On a finite-dimensional real normed space the transition semigroup that translates by `t • v` in
time `t` is a conservative Feller semigroup satisfying the Kolmogorov moment criterion with
exponents `p = q = 2` and constant `‖v‖²`.  The existence-and-uniqueness theorem of
`MarkovProcess.Main` therefore applies, and the process it produces is identified: from every
starting point `x` its law is the Dirac mass at the straight line `t ↦ x + t • v`.

Together with `MarkovProcess.Examples.Identity` this shows that the hypotheses of the main
theorem are satisfiable by a semigroup that genuinely moves.  Nothing here is claimed about a
semigroup with a nonzero diffusion part; for that see `MarkovProcess.Examples.HeatSemigroup`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]















open MarkovProcess in

theorem MarkovProcess.continuousProcess_driftSemigroup_eq (v : E) (x : E) :
    SubMarkovKernelSemigroup.IsConservative.continuousProcess (driftSemigroup v)
        (isConservative_driftSemigroup v) x =
      Measure.dirac (driftPath v x) := by sorry
