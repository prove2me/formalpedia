-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A5ForwardIndex_card_fiber_le
-- name    : OAI.UniqueGamesTheorem.Appendix.A5ForwardIndex.card_fiber_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:37:59.977997+00:00
-- url     : https://prove2.me/theorems/ce83946f-a721-41a0-a59f-0a9305f2af13
-- title:
--   OAI.UniqueGamesTheorem.Appendix.A5ForwardIndex.card_fiber_le: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Appendix.A5ForwardIndex.card_fiber_le` of [lean/OAI/Computability/UniqueGames/Analysis/A5FrequencyTransportLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/A5FrequencyTransportLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Appendix.A5ForwardIndex`, with `open UniqueGamesTheorem.Integration.BinaryLinear`, `open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)`, `open scoped BigOperators`):
--
--   ```lean
--   theorem card_fiber_le (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :
--       Nat.card (Fiber d r i j) ≤ 2 ^ (3 * (d * (i + j + targetRank r)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Appendix.A13Index.Triple` and `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Appendix.A5ForwardIndex.Fiber` and `OAI.UniqueGamesTheorem.Appendix.A5ForwardIndex.targetRank` (definitions bundle `OAIQ252P006` of this split).
--
--   **Used by.** The proof of `OAI.UniqueGamesTheorem.Appendix.A5Induction.derivative_inequality` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/A5FrequencyTransportLemmas.lean (declaration OAI.UniqueGamesTheorem.Appendix.A5ForwardIndex.card_fiber_le)

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
import Definitions.Def_OAIQ252P006

section

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

namespace Appendix.A5ForwardIndex

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.A5ForwardIndex.indexFintype
omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem card_fiber_le (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :
    Nat.card (Fiber d r i j) ≤ 2 ^ (3 * (d * (i + j + targetRank r))) := by
  sorry

end Appendix.A5ForwardIndex

end UniqueGamesTheorem

end

end OAI
end
