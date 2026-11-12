-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_WeightedFourthMoment_weighted_fourth_coefficient_energy
-- name    : OAI.UniqueGamesTheorem.Appendix.WeightedFourthMoment.weighted_fourth_coefficient_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:38:10.690304+00:00
-- url     : https://prove2.me/theorems/2b60b641-b16b-4b67-83f3-2cd36f7b2c56
-- title:
--   OAI.UniqueGamesTheorem.Appendix.WeightedFourthMoment.weighted_fourth_coefficient_energy: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Appendix.WeightedFourthMoment.weighted_fourth_coefficient_energy` of [lean/OAI/Computability/UniqueGames/Analysis/WeightedFourthMoment.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/WeightedFourthMoment.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Appendix.WeightedFourthMoment`, with `open Module`, `open scoped BigOperators`, `open UniqueGamesTheorem.Integration.BinaryLinear (F2)`, `open UniqueGamesTheorem.Appendix.RankAdditivity (RankBelow)`):
--
--   ```lean
--   theorem weighted_fourth_coefficient_energy (a : (E →ₗ[F2] F) → ℝ) (d : ℕ)
--       (hdegree : ∀ Y, d < rank Y → a Y = 0) :
--       (∑ X, ((2:ℝ)⁻¹)^(8*d*rank X)*(energy a X)^2) ≤ 2*(∑ Y, a Y^2)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Appendix.WeightedFourthMoment.energy` and `OAI.UniqueGamesTheorem.Appendix.WeightedFourthMoment.rank` (definitions bundle `OAIQ252P006` of this split).
--
--   **Used by.** The proof of `OAI.UniqueGamesTheorem.Appendix.A5Induction.recurrence_closure` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Analysis/WeightedFourthMoment.lean (declaration OAI.UniqueGamesTheorem.Appendix.WeightedFourthMoment.weighted_fourth_coefficient_energy)

import Lean.Elab.Tactic.Omega
import Mathlib
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
namespace UniqueGamesTheorem.Appendix.WeightedFourthMoment

open Module
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity (RankBelow)
attribute [local instance] Classical.propDecidable

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

theorem weighted_fourth_coefficient_energy (a : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    (∑ X, ((2:ℝ)⁻¹)^(8*d*rank X)*(energy a X)^2) ≤ 2*(∑ Y, a Y^2)^2 := by
  sorry

end UniqueGamesTheorem.Appendix.WeightedFourthMoment

end

end

end OAI
end
