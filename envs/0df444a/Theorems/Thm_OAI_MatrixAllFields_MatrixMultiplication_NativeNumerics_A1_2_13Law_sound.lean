-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A1_2_13Law_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_2_13Law_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:48:10.628751+00:00
-- url     : https://prove2.me/theorems/29ea1ede-da30-4c71-8fcc-2c6ae4752be6
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_2_13Law_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_2_13Law_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB2_3_3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB2_3_3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate`, `open scoped BigOperators`):
--
--   ```lean
--   lemma A1_2_13Law_sound (u : Shape) :
--       (A1_2_13Law u).Encloses (stageALaw (shape 1 2 13) u : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.stageALaw` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_2_13Law` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R11H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R12H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R13H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R14H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R15H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R16H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R3H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R4P_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R5Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R6Terms_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R7Terms_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R8Terms_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1R9H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB2_3_3.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_2_13Law_sound)

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

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A1_2_13Law_sound (u : Shape) :
    (A1_2_13Law u).Encloses (stageALaw (shape 1 2 13) u : ℝ) := by
  sorry

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end
