-- Prove2me | Theorems.Thm_OAI_Erdos970_WeightedTorusJets_Geometry_torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247
-- name    : OAI.Erdos970.WeightedTorusJets.Geometry.torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:58:06.065368+00:00
-- url     : https://prove2.me/theorems/bb294da9-cd22-43f3-b849-6c0e0697f44f
-- title:
--   OAI.Erdos970.WeightedTorusJets.Geometry.torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.WeightedTorusJets.Geometry.torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound` of [lean/OAI/NumberTheory/Jacobsthal/Siegel/TorusRectangleJetIdealParametersProjectiveDegreeBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/TorusRectangleJetIdealParametersProjectiveDegreeBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.WeightedTorusJets.Geometry`, with `open scoped _root_.Erdos970`):
--
--   ```lean
--   theorem torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247
--       (q : Ideal T₄) [q.IsPrime] (c : Fin 3 → Fin 4 → K) (t : Fin 3 → ℕ) (b : ℕ)
--       {N : ℕ} (hN : 0 < N) {F : P₄} (hF : F ∈ polynomialBox K N)
--       (hq : q ∈ (rectangleJetIdeal
--         (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).minimalPrimes) :
--       ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
--           (IsLocalRing.CotangentSpace (Localization.AtPrime q))) → P₄,
--         (∀ i, g i ∈ Submodule.span K
--           ((fun a => invariantJet c a F) '' {a | ∀ j, a j ≤ b * t j})) ∧
--         (∀ i, (g i).totalDegree ≤ 4 * N) ∧
--         (Ideal.span (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))).radical =
--           IsLocalRing.maximalIdeal (Localization.AtPrime q) ∧
--         Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸
--           (rectangleJetIdeal (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).map
--             (algebraMap T₄ (Localization.AtPrime q))) ≤
--           Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸ Ideal.span
--             (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))) ∧
--         Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸ Ideal.span
--             (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))) *
--           (GradedQuotient.projectiveDegree
--             (coneIdeal (q.comap (algebraMap P₄ T₄)))
--             (coneIdeal_isHomogeneous (q.comap (algebraMap P₄ T₄))) : ℕ∞) ≤
--           ((4 * N) ^ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
--             (IsLocalRing.CotangentSpace (Localization.AtPrime q)) : ℕ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.WeightedTorusJets.Geometry.coneIdeal`, `OAI.Erdos970.WeightedTorusJets.Geometry.coneIdeal_isHomogeneous`, `OAI.Erdos970.WeightedTorusJets.Geometry.invariantJet`, `OAI.Erdos970.WeightedTorusJets.Geometry.polynomialBox` and `OAI.Erdos970.WeightedTorusJets.Geometry.rectangleJetIdeal` (definitions bundle `OAIQ247J004` of this split); `OAI.Erdos970.WeightedTorusJets.Geometry.GradedQuotient.projectiveDegree` (definitions bundle `OAIQ247J007` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.WeightedTorusJets.actual_biquadratic_rectangle_span_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/TorusRectangleJetIdealParametersProjectiveDegreeBound.lean (declaration OAI.Erdos970.WeightedTorusJets.Geometry.torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound)

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
import Definitions.Def_OAIQ247J007

section

attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section
namespace WeightedTorusJets.Geometry

section TorusWeightedParameters

variable {K : Type*} [Field K] [Infinite K]
local notation "P₄" => MvPolynomial (Fin 4) K
local notation "T₄" => Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P₄))

theorem torus_rectangleJetIdeal_exists_parameters_with_projective_degree_bound_jb247
    (q : Ideal T₄) [q.IsPrime] (c : Fin 3 → Fin 4 → K) (t : Fin 3 → ℕ) (b : ℕ)
    {N : ℕ} (hN : 0 < N) {F : P₄} (hF : F ∈ polynomialBox K N)
    (hq : q ∈ (rectangleJetIdeal
      (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).minimalPrimes) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
        (IsLocalRing.CotangentSpace (Localization.AtPrime q))) → P₄,
      (∀ i, g i ∈ Submodule.span K
        ((fun a => invariantJet c a F) '' {a | ∀ j, a j ≤ b * t j})) ∧
      (∀ i, (g i).totalDegree ≤ 4 * N) ∧
      (Ideal.span (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ∧
      Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸
        (rectangleJetIdeal (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).map
          (algebraMap T₄ (Localization.AtPrime q))) ≤
        Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸ Ideal.span
          (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))) ∧
      Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸ Ideal.span
          (Set.range (fun i => algebraMap P₄ (Localization.AtPrime q) (g i)))) *
        (GradedQuotient.projectiveDegree
          (coneIdeal (q.comap (algebraMap P₄ T₄)))
          (coneIdeal_isHomogeneous (q.comap (algebraMap P₄ T₄))) : ℕ∞) ≤
        ((4 * N) ^ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
          (IsLocalRing.CotangentSpace (Localization.AtPrime q)) : ℕ) := by
  sorry

end TorusWeightedParameters

end WeightedTorusJets.Geometry

end

end

end Erdos970

end OAI
end
