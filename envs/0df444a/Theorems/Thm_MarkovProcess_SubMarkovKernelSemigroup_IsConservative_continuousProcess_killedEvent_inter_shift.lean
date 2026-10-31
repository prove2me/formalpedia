-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousProcess_killedEvent_inter_shift
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess_killedEvent_inter_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:43.322988+00:00
-- url     : https://prove2.me/theorems/160e5a11-4756-4e35-a0f5-cc4dcc82d366
-- title:
--   MarkovProcess: continuousProcess_killedEvent_inter_shift
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeterySemigroup_149c26e5
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_Killed_Process_a15f3c27
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
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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
import Mathlib.Topology.Constructions.SumProd
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
# Finite-dimensional distributions of the killed process

For the continuous-path process of a conservative Feller semigroup and an open set `U`, this file
identifies every finite-dimensional distribution of the process killed at the exit of `U`
(`killedProcess P hP U hU` of `Killed/Process.lean`, a law on lifetime paths in the carrier `U`)
with the corresponding finite-dimensional distribution of the **cemetery extension of the killed
semigroup** on `U`:

  `(killedProcess x).map (fun ω ↦ fun i : I ↦ coordinate i ω) =
      finiteSetKernel (cemeterySemigroup (killedSemigroup P hP U hU hFeller hK)) I (alive x)`

(`killedProcess_map_finiteEvaluation`), and, at a strictly increasing family of times, the
corresponding statement for `finiteTimeKernel` (`killedProcess_map_coordinates_ordered`).

The proof is by induction on the number of times, along the recursion of `finiteTimeKernel`.  The
induction step splits the survival event at the first time `t₁`: on `{t₁ < τ_U}` the later
coordinates of the killed path are the coordinates of the killed shifted path
(`coordinate_killAtExit_shift`), and the law of the shifted path is supplied by the restart
statement `continuousProcess_killedEvent_inter_shift` proved here, a form of the Markov property
at `t₁` restricted to the `𝓕_{t₁}`-event `{t₁ < τ_U} ∩ {ω t₁ ∈ B}`; on the complement every
coordinate is the cemetery state, matching the absorbing behaviour of the cemetery
(`finiteTimeKernel_cemeterySemigroup_delta`).  Measures on a finite product are compared on boxes.

No Feller property, strong continuity, or regularity of the killed semigroup is claimed, and no
statement here covers a random time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

section Dead

variable {beta : Type*} [MeasurableSpace beta] (S : SubMarkovKernelSemigroup beta)



end Dead


section Restart

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)



end Restart


section OrderedMarginals

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)



variable [LocallyCompactSpace alpha]
variable (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)





end OrderedMarginals

end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-dimensional distributions of the killed process

For the continuous-path process of a conservative Feller semigroup and an open set `U`, this file
identifies every finite-dimensional distribution of the process killed at the exit of `U`
(`killedProcess P hP U hU` of `Killed/Process.lean`, a law on lifetime paths in the carrier `U`)
with the corresponding finite-dimensional distribution of the **cemetery extension of the killed
semigroup** on `U`:

  `(killedProcess x).map (fun ω ↦ fun i : I ↦ coordinate i ω) =
      finiteSetKernel (cemeterySemigroup (killedSemigroup P hP U hU hFeller hK)) I (alive x)`

(`killedProcess_map_finiteEvaluation`), and, at a strictly increasing family of times, the
corresponding statement for `finiteTimeKernel` (`killedProcess_map_coordinates_ordered`).

The proof is by induction on the number of times, along the recursion of `finiteTimeKernel`.  The
induction step splits the survival event at the first time `t₁`: on `{t₁ < τ_U}` the later
coordinates of the killed path are the coordinates of the killed shifted path
(`coordinate_killAtExit_shift`), and the law of the shifted path is supplied by the restart
statement `continuousProcess_killedEvent_inter_shift` proved here, a form of the Markov property
at `t₁` restricted to the `𝓕_{t₁}`-event `{t₁ < τ_U} ∩ {ω t₁ ∈ B}`; on the complement every
coordinate is the cemetery state, matching the absorbing behaviour of the cemetery
(`finiteTimeKernel_cemeterySemigroup_delta`).  Measures on a finite product are compared on boxes.

No Feller property, strong continuity, or regularity of the killed semigroup is claimed, and no
statement here covers a random time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal






variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.continuousProcess_killedEvent_inter_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (t : NNReal) (x : U) {C : Set U} (hC : MeasurableSet C)
    {D : Set (ContinuousPath alpha)} (hD : MeasurableSet D) :
    IsConservative.continuousProcess P hP (x : alpha)
        (ContinuousPath.killedEvent U t (Subtype.val '' C) ∩ ContinuousPath.shift t ⁻¹' D) =
      ∫⁻ y in C, IsConservative.continuousProcess P hP (y : alpha) D
        ∂(IsConservative.killedKernelOn P hP U hU t x) := by sorry
