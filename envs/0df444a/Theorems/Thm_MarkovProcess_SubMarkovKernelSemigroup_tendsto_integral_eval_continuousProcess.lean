-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_tendsto_integral_eval_continuousProcess
-- name    : MarkovProcess.SubMarkovKernelSemigroup.tendsto_integral_eval_continuousProcess
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:33:51.99679+00:00
-- url     : https://prove2.me/theorems/a047c191-61da-442d-b280-f2652f3abbee
-- title:
--   MarkovProcess: tendsto_integral_eval_continuousProcess
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeConvergence_4d25bc20
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelCompactTestTransport_3904fd05
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Tight
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
# Convergence of the finite-dimensional distributions of Feller processes

Let `P i` be conservative Feller kernel semigroups and `Q` one more such semigroup, with
continuous-path processes `continuousProcess (P i)` and `continuousProcess Q`.  If the `C₀`
semigroups converge strongly -- by `Semigroup/TrotterKato.lean` this follows from convergence of
their resolvents at one
positive shift -- then the finite-dimensional distributions of the processes converge weakly from
every starting point: for every finite set `I` of times and every bounded continuous functional
of the coordinates at those times, the expectations converge.

The route is the identification of the finite-dimensional distributions with the finite-set
kernels (`continuousProcess_map_finiteEvaluation`), where the statement is
`Feller/FiniteSetConvergence.lean`.

Main results: `tendsto_integral_finsetEvaluation_continuousProcess`,
`tendsto_integral_eval_continuousProcess`.

Convergence of the finite-dimensional distributions is not convergence on path space, which needs
in addition a tightness estimate for the family of laws; that is not asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}





end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Convergence of the finite-dimensional distributions of Feller processes

Let `P i` be conservative Feller kernel semigroups and `Q` one more such semigroup, with
continuous-path processes `continuousProcess (P i)` and `continuousProcess Q`.  If the `C₀`
semigroups converge strongly -- by `Semigroup/TrotterKato.lean` this follows from convergence of
their resolvents at one
positive shift -- then the finite-dimensional distributions of the processes converge weakly from
every starting point: for every finite set `I` of times and every bounded continuous functional
of the coordinates at those times, the expectations converge.

The route is the identification of the finite-dimensional distributions with the finite-set
kernels (`continuousProcess_map_finiteEvaluation`), where the statement is
`Feller/FiniteSetConvergence.lean`.

Main results: `tendsto_integral_finsetEvaluation_continuousProcess`,
`tendsto_integral_eval_continuousProcess`.

Convergence of the finite-dimensional distributions is not convergence on path space, which needs
in addition a tightness estimate for the family of laws; that is not asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction NNReal ZeroAtInfty



open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}



open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.tendsto_integral_eval_continuousProcess
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hPK : ∀ i, (P i).KolmogorovRegular (hPc i))
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative) (hQK : Q.KolmogorovRegular hQc)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    (t : NNReal) (g : alpha →ᵇ ℝ) (x : alpha) :
    Tendsto (fun i ↦ ∫ omega, g (omega t) ∂(continuousProcess (P i) (hPc i) x)) l
      (nhds (∫ omega, g (omega t) ∂(continuousProcess Q hQc x))) := by sorry
