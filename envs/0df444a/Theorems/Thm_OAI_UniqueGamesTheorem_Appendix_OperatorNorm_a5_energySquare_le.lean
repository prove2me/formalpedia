-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_OperatorNorm_a5_energySquare_le
-- name    : OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a5_energySquare_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:38:13.820618+00:00
-- url     : https://prove2.me/theorems/768314c1-c38f-49b8-b0d8-8f778ff996c8
-- title:
--   OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a5_energySquare_le: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a5_energySquare_le` of [lean/OAI/Computability/UniqueGames/Analysis/HybridCompositionLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/HybridCompositionLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Appendix.OperatorNorm`, with `open scoped BigOperators`, `open UniqueGamesTheorem.Integration.BinaryLinear (F2)`, `open UniqueGamesTheorem.Fourier`, `open UniqueGamesTheorem.Appendix.Derivatives`, `open UniqueGamesTheorem.Appendix.OperatorPartitions`, `open UniqueGamesTheorem.Appendix.LinearIdentities`, `open UniqueGamesTheorem.Appendix.RankAdditivity`):
--
--   ```lean
--   theorem a5_energySquare_le (X : F →ₗ[F2] E)
--       (A : Submodule F2 E) (B : Submodule F2 F)
--       (hI : X.range ≤ A) (hB : B ≤ X.ker)
--       [Fintype (A5GeometricIndex X A B)]
--       (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
--       (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
--         S (mapDerivative X f) N ^ 2) ^ 2 ≤
--       (Fintype.card (A5GeometricIndex X A B) : ℝ) ^ 3 *
--         ∑ i : A5GeometricIndex X A B,
--           (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
--             (hybridDerivative i.val.1 i.val.2
--               (MatrixRestrictions.embed X.range X.ker S) f) N ^ 2) ^ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Appendix.OperatorNorm.compressedDualFintype`, `OAI.UniqueGamesTheorem.Appendix.OperatorNorm.quotientFinite`, `OAI.UniqueGamesTheorem.Appendix.OperatorPartitions.A5GeometricIndex`, `OAI.UniqueGamesTheorem.Appendix.OperatorPartitions.A5Geometry`, `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2`, `OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter`, `OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed` and `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Appendix.LinearIdentities.compress` (definitions bundle `OAIQ252P002` of this split); `OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype` (definitions bundle `OAIQ252P004` of this split); `OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridDerivative` and `OAI.UniqueGamesTheorem.Appendix.Derivatives.mapDerivative` (definitions bundle `OAIQ252P006` of this split).
--
--   **Used by.** The proof of `OAI.UniqueGamesTheorem.Appendix.A5Induction.boundedTripleSum_le_descendants` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/HybridCompositionLemmas.lean (declaration OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a5_energySquare_le)

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
theorem a5_energySquare_le (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    [Fintype (A5GeometricIndex X A B)]
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
      S (mapDerivative X f) N ^ 2) ^ 2 ≤
    (Fintype.card (A5GeometricIndex X A B) : ℝ) ^ 3 *
      ∑ i : A5GeometricIndex X A B,
        (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
          (hybridDerivative i.val.1 i.val.2
            (MatrixRestrictions.embed X.range X.ker S) f) N ^ 2) ^ 2 := by
  sorry

end UniqueGamesTheorem.Appendix.OperatorNorm

end

end

end OAI
end
