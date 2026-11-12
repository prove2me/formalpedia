-- Prove2me | Theorems.Thm_OAI_PerfectCompleteness_MatrixInverse_noiseEnergy_le_of_global
-- name    : OAI.PerfectCompleteness.MatrixInverse.noiseEnergy_le_of_global
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:47:31.758906+00:00
-- url     : https://prove2.me/theorems/785d905b-d5ab-4845-a975-c38bf6934c75
-- title:
--   OAI.PerfectCompleteness.MatrixInverse.noiseEnergy_le_of_global: intermediate lemma from OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PerfectCompleteness.MatrixInverse.noiseEnergy_le_of_global` of [lean/OAI/Computability/PerfectCompleteness/Algebra/MatrixInverse.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Algebra/MatrixInverse.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PerfectCompleteness.MatrixInverse`, with `open scoped BigOperators Classical`, `open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier`, `open UniqueGamesTheorem.Fourier.MatrixNoise UniqueGamesTheorem.Fourier.MatrixRestrictions`, `open UniqueGamesTheorem.Fourier.MatrixLevelBridge`, `open UniqueGamesTheorem.Appendix.LevelInequality UniqueGamesTheorem.Appendix.RankLevelFilter`):
--
--   ```lean
--   theorem noiseEnergy_le_of_global (r : Nat) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
--       (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
--       (hg : IsRestrictionGlobal f r ρ) :
--       noiseEnergy f ≤ (levelCutoffConstant r ρ + node (r + 1)) * (𝔼 X, f X ^ 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Fourier.MatrixCharacters.F2` (definitions bundle `OAIQ252P000` of this split); `OAI.UniqueGamesTheorem.Appendix.RankLevelFilter.node` and `OAI.UniqueGamesTheorem.Fourier.MatrixLevelBridge.levelCutoffConstant` (definitions bundle `OAIQ252P001` of this split); `OAI.UniqueGamesTheorem.Appendix.LevelInequality.IsBoolean` (definitions bundle `OAIQ252P002` of this split); `OAI.PerfectCompleteness.MatrixInverse.noiseEnergy` (definitions bundle `OAIQ252P006` of this split); `OAI.UniqueGamesTheorem.Appendix.LevelInequality.IsRestrictionGlobal` (definitions bundle `OAIQ252P011` of this split).
--
--   **Used by.** The proofs of `OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge` and `OAI.PerfectCompleteness.HierarchicalLowerInverse.matrixTable_agreement_lt` of this split import it.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Algebra/MatrixInverse.lean (declaration OAI.PerfectCompleteness.MatrixInverse.noiseEnergy_le_of_global)

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

attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixNoise UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.LevelInequality UniqueGamesTheorem.Appendix.RankLevelFilter

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem noiseEnergy_le_of_global (r : Nat) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (hg : IsRestrictionGlobal f r ρ) :
    noiseEnergy f ≤ (levelCutoffConstant r ρ + node (r + 1)) * (𝔼 X, f X ^ 2) := by
  sorry

end
end PerfectCompleteness.MatrixInverse

end

end OAI
end
