-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_initialRawBall_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialRawBall_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T05:53:08.088454+00:00
-- url     : https://prove2.me/theorems/25966590-1cbd-4ad6-9ab4-f2ac8434b026
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialRawBall_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialRawBall_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay`, `open scoped BigOperators`):
--
--   ```lean
--   lemma initialRawBall_sound (s : Shape) (hs : s ∈ sortedInitial) :
--       (initialRawBall s).Encloses (initialWeight s : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.initialWeight`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.sortedInitial` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialRawBall` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialDenominatorBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_0_16`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_1_15`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_2_14`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_3_13`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_4_12`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_5_11`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_0_6_10`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_1_14`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_2_13`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_3_12`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_4_11`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_1_5_10` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.initialRawBall_sound)

import Mathlib
import Definitions.Def_OAIQ254M003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropyCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open scoped BigOperators

lemma initialRawBall_sound (s : Shape) (hs : s ∈ sortedInitial) :
    (initialRawBall s).Encloses (initialWeight s : ℝ) := by
  sorry

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

end OAI
end
