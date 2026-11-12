-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_SelectorEnergy_hybridMomentSum_rankLevel_le
-- name    : OAI.UniqueGamesTheorem.Appendix.SelectorEnergy.hybridMomentSum_rankLevel_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:46:49.94465+00:00
-- url     : https://prove2.me/theorems/b6f2d5e2-6c74-4806-b176-d95500d97b89
-- title:
--   OAI.UniqueGamesTheorem.Appendix.SelectorEnergy.hybridMomentSum_rankLevel_le: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Appendix.SelectorEnergy.hybridMomentSum_rankLevel_le` of [lean/OAI/Computability/PerfectCompleteness/Foundations/GlobalityLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/GlobalityLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Appendix.SelectorEnergy`, with `open scoped BigOperators`, `open UniqueGamesTheorem.Integration.BinaryLinear (F2)`, `open UniqueGamesTheorem.Fourier.MatrixFourier`):
--
--   ```lean
--   theorem hybridMomentSum_rankLevel_le (d : ℕ) (η : ℝ)
--       (f : (E →ₗ[F2] F) → ℝ) (hf : LevelInequality.IsRestrictionGlobal f d η) :
--       Derivatives.hybridMomentSum d (LevelInequality.rankLevel d f) ≤
--         (2 : ℝ) ^ (13 * d * d) * η * (𝔼 X, f X ^ 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Appendix.LevelInequality.rankLevel` (definitions bundle `OAIQ252P006` of this split); `OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridMomentSum` and `OAI.UniqueGamesTheorem.Appendix.LevelInequality.IsRestrictionGlobal` (definitions bundle `OAIQ252P011` of this split).
--
--   **Used by.** The proof of `OAI.PerfectCompleteness.MatrixInverse.noiseEnergy_le_of_global` of this split imports it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Foundations/GlobalityLemmas.lean (declaration OAI.UniqueGamesTheorem.Appendix.SelectorEnergy.hybridMomentSum_rankLevel_le)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P011

section

attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

namespace UniqueGamesTheorem.Appendix.SelectorEnergy

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem hybridMomentSum_rankLevel_le (d : ℕ) (η : ℝ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : LevelInequality.IsRestrictionGlobal f d η) :
    Derivatives.hybridMomentSum d (LevelInequality.rankLevel d f) ≤
      (2 : ℝ) ^ (13 * d * d) * η * (𝔼 X, f X ^ 2) := by
  sorry

end UniqueGamesTheorem.Appendix.SelectorEnergy

end

end

end OAI
end
