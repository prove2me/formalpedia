-- Prove2me | Theorems.Thm_OAI_Erdos970_WeightedTorusJets_Geometry_DegreeBezout_linear_normalization_weighted_local_length_le_jb247
-- name    : OAI.Erdos970.WeightedTorusJets.Geometry.DegreeBezout.linear_normalization_weighted_local_length_le_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:39:53.348392+00:00
-- url     : https://prove2.me/theorems/f605fba7-e6d7-4868-8e0c-3f8a51f1a40a
-- title:
--   OAI.Erdos970.WeightedTorusJets.Geometry.DegreeBezout.linear_normalization_weighted_local_length_le_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.WeightedTorusJets.Geometry.DegreeBezout.linear_normalization_weighted_local_length_le` of [lean/OAI/NumberTheory/Jacobsthal/Siegel/LinearVariableBasis.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/LinearVariableBasis.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.WeightedTorusJets.Geometry.DegreeBezout`, with `open scoped BigOperators`, `open Module`, `open MvPolynomial`, `open scoped BigOperators`, `open scoped BigOperators`, `open MvPolynomial`, `open Module TensorProduct`):
--
--   ```lean
--   theorem linear_normalization_weighted_local_length_le_jb247
--       {K σ : Type*} [Field K] [Finite σ] {s h D : ℕ}
--       (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
--       (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial σ K ⧸ P))
--       (hg : Function.Injective g)
--       (hfinite : letI := g.toAlgebra
--         letI : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
--         Module.Finite (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P))
--       (hlin : ∀ i, ∃ l : MvPolynomial σ K,
--         l.IsHomogeneous 1 ∧ g (MvPolynomial.X i) = Ideal.Quotient.mk P l)
--       (hcount : s + h = Nat.card σ)
--       (f : Fin h → MvPolynomial σ K)
--       (hf : ∀ i, (f i).totalDegree ≤ D)
--       (hrad : (Ideal.span (Set.range (fun i =>
--         algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (f i)))).radical =
--           IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
--       letI := g.toAlgebra
--       letI : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
--       Module.length (Localization.AtPrime P)
--         (Localization.AtPrime P ⧸ Ideal.span (Set.range (fun i =>
--           algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (f i)))) *
--         (Module.finrank (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) : ℕ∞) ≤
--           (D ^ h : ℕ)
--   ```
--
--   **Used by.** The proofs of `OAI_Erdos970_WeightedTorusJets_Geometry_local_length_mul_projectiveClosure_degree_le_jb247` and `OAI.Erdos970.WeightedTorusJets.Geometry.torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/LinearVariableBasis.lean (declaration OAI.Erdos970.WeightedTorusJets.Geometry.DegreeBezout.linear_normalization_weighted_local_length_le)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open Module TensorProduct

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem linear_normalization_weighted_local_length_le_jb247
    {K σ : Type*} [Field K] [Finite σ] {s h D : ℕ}
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : Function.Injective g)
    (hfinite : letI := g.toAlgebra
      letI : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
      Module.Finite (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P))
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (MvPolynomial.X i) = Ideal.Quotient.mk P l)
    (hcount : s + h = Nat.card σ)
    (f : Fin h → MvPolynomial σ K)
    (hf : ∀ i, (f i).totalDegree ≤ D)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    letI := g.toAlgebra
    letI : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ Ideal.span (Set.range (fun i =>
        algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (f i)))) *
      (Module.finrank (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) : ℕ∞) ≤
        (D ^ h : ℕ) := by
  sorry

end WeightedTorusJets.Geometry.DegreeBezout

end
end
end
end
end

end

end Erdos970

end OAI
end
