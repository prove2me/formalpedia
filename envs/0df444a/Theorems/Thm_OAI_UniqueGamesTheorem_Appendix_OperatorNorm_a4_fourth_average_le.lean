-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_OperatorNorm_a4_fourth_average_le
-- name    : OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a4_fourth_average_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:16:22.143227+00:00
-- url     : https://prove2.me/theorems/db7cb614-6de7-4759-9588-0c5c6e7d69fb
-- title:
--   OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a4_fourth_average_le: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a4_fourth_average_le` of [lean/OAI/Computability/UniqueGames/Analysis/HybridCompositionLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/HybridCompositionLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Appendix.OperatorNorm`, with `open scoped BigOperators`, `open UniqueGamesTheorem.Integration.BinaryLinear (F2)`, `open UniqueGamesTheorem.Fourier`, `open UniqueGamesTheorem.Appendix.Derivatives`, `open UniqueGamesTheorem.Appendix.OperatorPartitions`, `open UniqueGamesTheorem.Appendix.LinearIdentities`, `open UniqueGamesTheorem.Appendix.RankAdditivity`):
--
--   ```lean
--   theorem a4_fourth_average_le (A : Submodule F2 E) (B : Submodule F2 F)
--       [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
--       (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
--       (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
--         ∑ i : A4GeometricIndex A B,
--           𝔼 T, 𝔼 N, mapDerivative i.val.2.2
--             (hybridDerivative i.val.1 i.val.2.1 T f) N ^ 4
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Appendix.A4IndexCount.Valid`, `OAI.UniqueGamesTheorem.Appendix.LinearIdentities.A4Index`, `OAI.UniqueGamesTheorem.Appendix.OperatorNorm.compressedDualFintype`, `OAI.UniqueGamesTheorem.Appendix.OperatorNorm.quotientFinite`, `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2`, `OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter` and `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype` (definitions bundle `OAIQ252P004` of this split); `OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridDerivative`, `OAI.UniqueGamesTheorem.Appendix.Derivatives.mapDerivative`, `OAI.UniqueGamesTheorem.Appendix.Derivatives.spectralProjector` and `OAI.UniqueGamesTheorem.Appendix.OperatorPartitions.A4GeometricIndex` (definitions bundle `OAIQ252P006` of this split).
--
--   **Used by.** The proof of `OAI.UniqueGamesTheorem.Appendix.A13Reduction.weakFourthSum_le_positiveTripleSum` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/HybridCompositionLemmas.lean (declaration OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a4_fourth_average_le)

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
import Definitions.Def_OAIQ252P004
import Definitions.Def_OAIQ252P006

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
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
open UniqueGamesTheorem.Appendix.RankAdditivity

namespace UniqueGamesTheorem.Appendix.OperatorNorm

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.OperatorNorm.quotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.OperatorNorm.compressedDualFintype
theorem a4_fourth_average_le (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
    (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
      ∑ i : A4GeometricIndex A B,
        𝔼 T, 𝔼 N, mapDerivative i.val.2.2
          (hybridDerivative i.val.1 i.val.2.1 T f) N ^ 4 := by
  sorry

end UniqueGamesTheorem.Appendix.OperatorNorm

end

end

end OAI
end
