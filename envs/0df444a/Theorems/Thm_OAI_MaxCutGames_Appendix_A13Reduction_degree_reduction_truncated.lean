-- Prove2me | Theorems.Thm_OAI_MaxCutGames_Appendix_A13Reduction_degree_reduction_truncated
-- name    : OAI.MaxCutGames.Appendix.A13Reduction.degree_reduction_truncated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:43:08.800997+00:00
-- url     : https://prove2.me/theorems/649c8c54-eb06-4e9c-9f72-950c753cf27b
-- title:
--   OAI.MaxCutGames.Appendix.A13Reduction.degree_reduction_truncated: intermediate lemma from OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaxCutGames.Appendix.A13Reduction.degree_reduction_truncated` of [lean/OAI/Computability/MaxCut/Games/A1Reduction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/A1Reduction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaxCutGames.Appendix.A13Reduction`, with `open scoped BigOperators`, `open MaxCutGames.Integration.BinaryLinear (F2)`, `open MaxCutGames.Fourier`, `open MaxCutGames.Appendix.Derivatives`, `open MaxCutGames.Appendix.OperatorPartitions`, `open MaxCutGames.Appendix.LinearIdentities`):
--
--   ```lean
--   theorem degree_reduction_truncated (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
--       (hf : DerivativeDegree.DegreeAtMost d f) :
--       (𝔼 M, f M ^ 4) / 162 ≤
--         (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + boundedPositiveTripleSum d f
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaxCutGames.Appendix.A13Reduction.boundedPositiveTripleSum`, `OAI.MaxCutGames.Appendix.DerivativeDegree.DegreeAtMost` and `OAI.MaxCutGames.Integration.BinaryLinear.F2` (definitions bundle `OAIQ087A000` of this split).
--
--   **Used by.** The proof of `OAI.MaxCutGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid` of this split imports it.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/A1Reduction.lean (declaration OAI.MaxCutGames.Appendix.A13Reduction.degree_reduction_truncated)

import Mathlib
import Definitions.Def_OAIQ087A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.OperatorPartitions
open MaxCutGames.Appendix.LinearIdentities

namespace MaxCutGames.Appendix.A13Reduction

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

end MaxCutGames.Appendix.A13Reduction
end

end OAI
end
