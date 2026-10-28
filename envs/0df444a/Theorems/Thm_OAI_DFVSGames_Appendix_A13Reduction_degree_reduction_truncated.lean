-- Prove2me | Theorems.Thm_OAI_DFVSGames_Appendix_A13Reduction_degree_reduction_truncated
-- name    : OAI.DFVSGames.Appendix.A13Reduction.degree_reduction_truncated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:38:35.066377+00:00
-- url     : https://prove2.me/theorems/46d69a7f-c5fd-4b87-8a20-f64456543a5c
-- title:
--   OAI.DFVSGames.Appendix.A13Reduction.degree_reduction_truncated: intermediate lemma from OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DFVSGames.Appendix.A13Reduction.degree_reduction_truncated` of [lean/OAI/Computability/DirectedFeedback/Probability/A13Reduction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Probability/A13Reduction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DFVSGames.Appendix.A13Reduction`, with `open scoped BigOperators`, `open DFVSGames.Integration.BinaryLinear (F2)`, `open DFVSGames.Fourier`, `open DFVSGames.Appendix.Derivatives`, `open DFVSGames.Appendix.OperatorPartitions`, `open DFVSGames.Appendix.LinearIdentities`):
--
--   ```lean
--   theorem degree_reduction_truncated (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
--       (hf : DerivativeDegree.DegreeAtMost d f) :
--       (𝔼 M, f M ^ 4) / 162 ≤
--         (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + boundedPositiveTripleSum d f
--   ```
--
--   **Definitions.** The statement is written with `OAI.DFVSGames.Integration.BinaryLinear.F2` (definitions bundle `OAIQ085D000` of this split); `OAI.DFVSGames.Appendix.A13Reduction.boundedPositiveTripleSum` and `OAI.DFVSGames.Appendix.DerivativeDegree.DegreeAtMost` (definitions bundle `OAIQ085D018` of this split).
--
--   **Used by.** The proof of `OAI.DFVSGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid` of this split imports it.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Probability/A13Reduction.lean (declaration OAI.DFVSGames.Appendix.A13Reduction.degree_reduction_truncated)

import Mathlib
import Definitions.Def_OAIQ085D018

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Fourier
open DFVSGames.Appendix.Derivatives
open DFVSGames.Appendix.OperatorPartitions
open DFVSGames.Appendix.LinearIdentities

namespace DFVSGames.Appendix.A13Reduction

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

end DFVSGames.Appendix.A13Reduction
end

end OAI
end
