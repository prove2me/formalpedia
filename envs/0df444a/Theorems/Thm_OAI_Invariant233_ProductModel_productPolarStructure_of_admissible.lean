-- Prove2me | Theorems.Thm_OAI_Invariant233_ProductModel_productPolarStructure_of_admissible
-- name    : OAI.Invariant233.ProductModel.productPolarStructure_of_admissible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:19:54.248301+00:00
-- url     : https://prove2.me/theorems/8203a183-0116-42c1-b538-cac104420ebc
-- title:
--   OAI.Invariant233.ProductModel.productPolarStructure_of_admissible: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Invariant233.Results.prescribed_irrational_counterexample` and `OAI.Invariant233.Results.product_realization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Invariant233.ProductModel.productPolarStructure_of_admissible` of [lean/OAI/Analysis/IrrationalRotation/Spectral/ProductPolarComplete.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Spectral/ProductPolarComplete.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Invariant233.ProductModel`, with `open MeasureTheory Set`, `open scoped ENNReal`):
--
--   ```lean
--   theorem productPolarStructure_of_admissible
--       (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c) :
--       ProductPolarStructure shiftOperator (weightedOperator θ c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Invariant233.Circle`, `OAI.Invariant233.ProductPolarStructure`, `OAI.Invariant233.ProductModel.AdmissibleAnglesAndCosts`, `OAI.Invariant233.ProductModel.Base`, `OAI.Invariant233.ProductModel.Fiber`, `OAI.Invariant233.ProductModel.Hilbert`, `OAI.Invariant233.ProductModel.baseMeasure`, `OAI.Invariant233.ProductModel.shiftOperator` and `OAI.Invariant233.ProductModel.weightedOperator` (the published bundle `Def_IrrationalRotation`).
--
--   **Used by.** The proof of `OAI.Invariant233.ProductModel.product_realization_of_ae_sampling` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/IrrationalRotation/Spectral/ProductPolarComplete.lean (declaration OAI.Invariant233.ProductModel.productPolarStructure_of_admissible)

import Mathlib
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Set.Countable
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
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
open scoped ENNReal

namespace Invariant233.ProductModel

theorem productPolarStructure_of_admissible
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  sorry

end Invariant233.ProductModel

end

end OAI
end
