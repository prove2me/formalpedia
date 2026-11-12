-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A13Reduction_degree_reduction_truncated
-- name    : OAI.UniqueGamesTheorem.Appendix.A13Reduction.degree_reduction_truncated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:46:14.584471+00:00
-- url     : https://prove2.me/theorems/34a2bddc-6bd0-4165-9d99-ae343a6cdb4c
-- title:
--   OAI.UniqueGamesTheorem.Appendix.A13Reduction.degree_reduction_truncated: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Appendix.A13Reduction.degree_reduction_truncated` of [lean/OAI/Computability/UniqueGames/Analysis/HybridCompositionLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/HybridCompositionLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Appendix.A13Reduction`, with `open scoped BigOperators`, `open UniqueGamesTheorem.Integration.BinaryLinear (F2)`, `open UniqueGamesTheorem.Fourier`, `open UniqueGamesTheorem.Appendix.Derivatives`, `open UniqueGamesTheorem.Appendix.OperatorPartitions`, `open UniqueGamesTheorem.Appendix.LinearIdentities`):
--
--   ```lean
--   theorem degree_reduction_truncated (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
--       (hf : DerivativeDegree.DegreeAtMost d f) :
--       (𝔼 M, f M ^ 4) / 162 ≤
--         (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + boundedPositiveTripleSum d f
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Appendix.DerivativeDegree.DegreeAtMost` (definitions bundle `OAIQ252P006` of this split); `OAI.UniqueGamesTheorem.Appendix.A13Reduction.boundedPositiveTripleSum` (definitions bundle `OAIQ252P011` of this split).
--
--   **Used by.** The proof of `OAI.UniqueGamesTheorem.Appendix.A5Induction.derivative_inequality` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/HybridCompositionLemmas.lean (declaration OAI.UniqueGamesTheorem.Appendix.A13Reduction.degree_reduction_truncated)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P011

section

attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities

namespace UniqueGamesTheorem.Appendix.A13Reduction

attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

theorem degree_reduction_truncated (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + boundedPositiveTripleSum d f := by
  sorry

end UniqueGamesTheorem.Appendix.A13Reduction

end

end

end OAI
end
