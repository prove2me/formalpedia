-- Prove2me | Theorems.Thm_MarkovProcess_dist_le_two_heatExhaustion
-- name    : MarkovProcess.dist_le_two_heatExhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:45.29927+00:00
-- url     : https://prove2.me/theorems/38482db6-d3e6-4f99-97eb-e3407233469c
-- title:
--   MarkovProcess: dist_le_two_heatExhaustion
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Examples_HeatOnePoint_42235b58
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
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
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The compactified heat process

The heat resolvent represents the heat semigroup again
(`kernelSemigroup_heatResolvent`), so its one-point extension moves a live starting point by the
Gaussian law and never reaches the added point.  In the metric determined by the exhaustion
`x ↦ 1 / (1 + |x|)` the distance of two points is at most `2` and the distance of two live points
is at most their distance on the line, so the fourth-moment estimate of the Gaussian law gives
the local Kolmogorov criterion on the compactification
(`hasLocalKolmogorovMoments_onePointKernelSemigroup_heatResolvent`).

This assembles the regularity data from which the continuous-path process of the compactified
heat semigroup is formed (`onePointRegular_heatResolvent`), the witness that those data are
available for a genuine example.  Because the heat semigroup is conservative, the compactified
process started at a live point almost surely never reaches the added point
(`ae_exitTime_eq_top_heatResolvent`).
-/

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess



section Metric





end Metric

section Moments



end Moments





end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The compactified heat process

The heat resolvent represents the heat semigroup again
(`kernelSemigroup_heatResolvent`), so its one-point extension moves a live starting point by the
Gaussian law and never reaches the added point.  In the metric determined by the exhaustion
`x ↦ 1 / (1 + |x|)` the distance of two points is at most `2` and the distance of two live points
is at most their distance on the line, so the fourth-moment estimate of the Gaussian law gives
the local Kolmogorov criterion on the compactification
(`hasLocalKolmogorovMoments_onePointKernelSemigroup_heatResolvent`).

This assembles the regularity data from which the continuous-path process of the compactified
heat semigroup is formed (`onePointRegular_heatResolvent`), the witness that those data are
available for a genuine example.  Because the heat semigroup is conservative, the compactified
process started at a live point almost surely never reaches the added point
(`ae_exitTime_eq_top_heatResolvent`).
-/

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty






open MarkovProcess in

theorem MarkovProcess.dist_le_two_heatExhaustion (z w : OnePoint ℝ) :
    letI := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    dist z w ≤ 2 := by sorry
