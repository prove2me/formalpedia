-- Prove2me | Theorems.Thm_OAI_Erdos970_WeightedTorusJets_conductorCompletedL_hadamard_factorization_jb247
-- name    : OAI.Erdos970.WeightedTorusJets.conductorCompletedL_hadamard_factorization_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:49:02.614421+00:00
-- url     : https://prove2.me/theorems/2bdb3127-12db-443a-93bb-4cc72890ffde
-- title:
--   OAI.Erdos970.WeightedTorusJets.conductorCompletedL_hadamard_factorization_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.WeightedTorusJets.conductorCompletedL_hadamard_factorization` of [lean/OAI/NumberTheory/Jacobsthal/Siegel/ConductorCompletedL.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/ConductorCompletedL.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.WeightedTorusJets`, with `open scoped _root_.Erdos970`, `open scoped BigOperators Topology`, `open _root_.Filter _root_.Set _root_.MeasureTheory`, `open scoped Topology`, `open _root_.Filter _root_.Set _root_.Asymptotics`, `open _root_.Erdos970.Complex.Hadamard`):
--
--   ```lean
--   theorem conductorCompletedL_hadamard_factorization_jb247 (χ : DirichletCharacter ℂ q)
--       (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
--       ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ s : ℂ,
--         conductorCompletedL χ s = Complex.exp (P.eval s) *
--           divisorCanonicalProduct 1 (conductorCompletedL χ) (Set.univ : Set ℂ) s
--   ```
--
--   **Definitions.** The statement is written with `Erdos970.Complex.Hadamard.divisorCanonicalProduct` (definitions bundle `OAIQ247J000` of this split); `OAI.Erdos970.WeightedTorusJets.conductorCompletedL` (definitions bundle `OAIQ247J005` of this split).
--
--   **Used by.** The proof of `OAI.Erdos970.WeightedTorusJets.conductorCompletedL_logDeriv_hasSum_jb247` of this split imports it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/ConductorCompletedL.lean (declaration OAI.Erdos970.WeightedTorusJets.conductorCompletedL_hadamard_factorization)

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
import Definitions.Def_OAIQ247J000
import Definitions.Def_OAIQ247J005

section

attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section AnalyticAssemblyScope
open scoped BigOperators Topology
section
open _root_.Filter _root_.Set _root_.MeasureTheory
open scoped Topology
open _root_.Filter _root_.Set _root_.Asymptotics

namespace WeightedTorusJets

open _root_.Erdos970.Complex.Hadamard

variable {q : ℕ} [NeZero q]

theorem conductorCompletedL_hadamard_factorization_jb247 (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ s : ℂ,
      conductorCompletedL χ s = Complex.exp (P.eval s) *
        divisorCanonicalProduct 1 (conductorCompletedL χ) (Set.univ : Set ℂ) s := by
  sorry

end WeightedTorusJets

end
end AnalyticAssemblyScope
end

end Erdos970

end OAI
end
