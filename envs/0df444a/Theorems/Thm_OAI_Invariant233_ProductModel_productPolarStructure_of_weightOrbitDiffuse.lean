-- Prove2me | Theorems.Thm_OAI_Invariant233_ProductModel_productPolarStructure_of_weightOrbitDiffuse
-- name    : OAI.Invariant233.ProductModel.productPolarStructure_of_weightOrbitDiffuse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:19:54.44375+00:00
-- url     : https://prove2.me/theorems/7a9f686c-107e-4fee-86f7-4eb1eabdb29c
-- title:
--   OAI.Invariant233.ProductModel.productPolarStructure_of_weightOrbitDiffuse: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.ProductModel.productPolarStructure_of_weightOrbitDiffuse` of [lean/OAI/Analysis/IrrationalRotation/Spectral/ProductPolarAssembly.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Spectral/ProductPolarAssembly.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.ProductModel`, with `open MeasureTheory Set`):
--
--   ```lean
--   theorem productPolarStructure_of_weightOrbitDiffuse
--       (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
--       (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
--       (hdiff : IsDiffuseVonNeumannAlgebra
--         (fullPolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c))) :
--       ProductPolarStructure shiftOperator (weightedOperator θ c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.Circle`, `OAI.Invariant233.IsDiffuseVonNeumannAlgebra`, `OAI.Invariant233.ProductPolarStructure`, `OAI.Invariant233.fullPolarAlgebra`, `OAI.Invariant233.ProductModel.Base`, `OAI.Invariant233.ProductModel.Fiber`, `OAI.Invariant233.ProductModel.Hilbert`, `OAI.Invariant233.ProductModel.baseMeasure`, `OAI.Invariant233.ProductModel.instAddCommMonoidProductWeightedOperator`, `OAI.Invariant233.ProductModel.instModuleProductWeightedOperator`, `OAI.Invariant233.ProductModel.instTopologicalSpaceProductWeightedOperator`, `OAI.Invariant233.ProductModel.shiftOperator` and `OAI.Invariant233.ProductModel.weightedOperator` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.ProductModel.productPolarStructure_of_admissible` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Spectral/ProductPolarAssembly.lean (declaration OAI.Invariant233.ProductModel.productPolarStructure_of_weightOrbitDiffuse)

import Mathlib
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Definitions.Def_IrrationalRotation

section

attribute [-instance] _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductModel

theorem productPolarStructure_of_weightOrbitDiffuse
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hdiff : IsDiffuseVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c))) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  sorry

end Invariant233.ProductModel

end

end OAI
end
