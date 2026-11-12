-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_BadConvolution_badConvolution_sq_sum_le
-- name    : OAI.UniqueGamesTheorem.Appendix.BadConvolution.badConvolution_sq_sum_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:38:05.697196+00:00
-- url     : https://prove2.me/theorems/8ee0e473-1ee7-4ed3-a1f1-16ec8d591e6d
-- title:
--   OAI.UniqueGamesTheorem.Appendix.BadConvolution.badConvolution_sq_sum_le: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Appendix.BadConvolution.badConvolution_sq_sum_le` of [lean/OAI/Computability/UniqueGames/Analysis/BadConvolution.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/BadConvolution.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Appendix.BadConvolution`, with `open scoped BigOperators`, `open UniqueGamesTheorem.Integration.BinaryLinear (F2)`, `open Module (finrank)`):
--
--   ```lean
--   theorem badConvolution_sq_sum_le
--       (a : (W →ₗ[F2] V) → ℝ) (d : ℕ) (hd : 1 ≤ d)
--       (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0) :
--       (∑ X, badConvolution a X ^ 2) ≤
--         ∑ p : Submodule F2 V × Submodule F2 W,
--           if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*(finrank F2 p.1 + finrank F2 (W ⧸ p.2))) *
--             (∑ X, pieceConvolution p.1 p.2 a X ^ 2) else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Appendix.BadConvolution.badConvolution` and `OAI.UniqueGamesTheorem.Appendix.BadConvolution.pieceConvolution` (definitions bundle `OAIQ252P006` of this split).
--
--   **Used by.** The proof of `OAI.UniqueGamesTheorem.Appendix.A13Reduction.degree_reduction_truncated` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/BadConvolution.lean (declaration OAI.UniqueGamesTheorem.Appendix.BadConvolution.badConvolution_sq_sum_le)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P006

section

attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.BadConvolution
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open Module (finrank)
attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

variable [Finite W] [Finite V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

variable [Fintype (W →ₗ[F2] V)]

theorem badConvolution_sq_sum_le
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0) :
    (∑ X, badConvolution a X ^ 2) ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*(finrank F2 p.1 + finrank F2 (W ⧸ p.2))) *
          (∑ X, pieceConvolution p.1 p.2 a X ^ 2) else 0 := by
  sorry

end UniqueGamesTheorem.Appendix.BadConvolution

end

end

end OAI
end
