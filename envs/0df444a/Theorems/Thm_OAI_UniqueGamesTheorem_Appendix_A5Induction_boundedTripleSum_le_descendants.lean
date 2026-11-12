-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A5Induction_boundedTripleSum_le_descendants
-- name    : OAI.UniqueGamesTheorem.Appendix.A5Induction.boundedTripleSum_le_descendants
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:48:57.096084+00:00
-- url     : https://prove2.me/theorems/9b59a198-668f-464f-85c2-d21335a477e9
-- title:
--   OAI.UniqueGamesTheorem.Appendix.A5Induction.boundedTripleSum_le_descendants: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Appendix.A5Induction.boundedTripleSum_le_descendants` of [lean/OAI/Computability/UniqueGames/Analysis/A5FrequencyTransportLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/A5FrequencyTransportLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Appendix.A5Induction`, with `open scoped BigOperators`, `open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier`, `open UniqueGamesTheorem.Fourier.MatrixRestrictions`, `open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.DerivativeDegree`, `open UniqueGamesTheorem.Appendix.LevelInequality (frequencyRank)`):
--
--   ```lean
--   theorem boundedTripleSum_le_descendants (d : ℕ)
--       (ih : ∀ e, e < d → BoundAtDegree.{u, v} e)
--       (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
--       A13Reduction.boundedPositiveTripleSum d f ≤
--         ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
--           (2 : ℝ) ^ (100 * (d - A13Index.size p.val)^2 +
--             24 * d * A13Index.size p.val + 6 * d * Module.finrank F2 p.val.2.2.range) *
--             A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
--               (d - A13Index.size p.val) f
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Appendix.A13Index.BoundedPositiveTriple`, `OAI.UniqueGamesTheorem.Appendix.A13Index.Triple`, `OAI.UniqueGamesTheorem.Appendix.A13Index.size`, `OAI.UniqueGamesTheorem.Appendix.OperatorNorm.compressedDualFintype`, `OAI.UniqueGamesTheorem.Appendix.SubspaceExtensions.subspaceFintype`, `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2` and `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Appendix.DerivativeDegree.DegreeAtMost` (definitions bundle `OAIQ252P006` of this split); `OAI.UniqueGamesTheorem.Appendix.A13Reduction.boundedPositiveTripleSum`, `OAI.UniqueGamesTheorem.Appendix.A5Induction.BoundAtDegree` and `OAI.UniqueGamesTheorem.Appendix.A5Passage.descendantSum` (definitions bundle `OAIQ252P011` of this split).
--
--   **Used by.** The proof of `OAI.UniqueGamesTheorem.Appendix.A5Induction.derivative_inequality` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/A5FrequencyTransportLemmas.lean (declaration OAI.UniqueGamesTheorem.Appendix.A5Induction.boundedTripleSum_le_descendants)

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

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

namespace Appendix.A5Induction

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.DerivativeDegree
open UniqueGamesTheorem.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

universe u v

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Finite E] [Finite F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem boundedTripleSum_le_descendants (d : ℕ)
    (ih : ∀ e, e < d → BoundAtDegree.{u, v} e)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    A13Reduction.boundedPositiveTripleSum d f ≤
      ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
        (2 : ℝ) ^ (100 * (d - A13Index.size p.val)^2 +
          24 * d * A13Index.size p.val + 6 * d * Module.finrank F2 p.val.2.2.range) *
          A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
            (d - A13Index.size p.val) f := by
  sorry

end Appendix.A5Induction

end UniqueGamesTheorem

end

end OAI
end
