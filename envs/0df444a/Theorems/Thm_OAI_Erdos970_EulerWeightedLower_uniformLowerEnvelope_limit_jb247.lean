-- Prove2me | Theorems.Thm_OAI_Erdos970_EulerWeightedLower_uniformLowerEnvelope_limit_jb247
-- name    : OAI.Erdos970.EulerWeightedLower.uniformLowerEnvelope_limit_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:47:45.552832+00:00
-- url     : https://prove2.me/theorems/e0ab1607-cfc6-4173-844d-4cfbff8814a1
-- title:
--   OAI.Erdos970.EulerWeightedLower.uniformLowerEnvelope_limit_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.EulerWeightedLower.uniformLowerEnvelope_limit` of [lean/OAI/NumberTheory/Jacobsthal/Estimates/UniformLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Estimates/UniformLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.EulerWeightedLower`, with `open Erdos970.EulerPrimeLaw _root_.Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem uniformLowerEnvelope_limit_jb247 :
--       Tendsto uniformLowerEnvelope atTop
--         (𝓝 (Real.exp (-Real.eulerMascheroniConstant) * (94 / 100 : ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.EulerWeightedLower.uniformLowerEnvelope` (definitions bundle `OAIQ247J003` of this split).
--
--   **Used by.** The proofs of `OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247` and `OAI_Erdos970_EulerWeightedLower_weightedSmallSum_eventually_uniform_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Estimates/UniformLower.lean (declaration OAI.Erdos970.EulerWeightedLower.uniformLowerEnvelope_limit)

import Mathlib
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic
import Definitions.Def_OAIQ247J003

section

attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw _root_.Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem uniformLowerEnvelope_limit_jb247 :
    Tendsto uniformLowerEnvelope atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant) * (94 / 100 : ℝ))) := by
  sorry

end EulerWeightedLower

end Erdos970

end OAI
end
