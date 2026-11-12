-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B4_1_3Den_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Den_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:21:29.529202+00:00
-- url     : https://prove2.me/theorems/fa52ae57-226f-48c0-a0c9-e772f30f8c34
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Den_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Den_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/Terminal4_1_3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/Terminal4_1_3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate`, `open scoped BigOperators`):
--
--   ```lean
--   lemma B4_1_3Den_sound : B4_1_3Den.Encloses (((below (shape 4 1 3)).map (splitWeight positiveSecond tablep (shape 4 1 3))).sum : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.below`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.positiveSecond`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.splitWeight`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.tablep` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Den` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1PairMassTerm_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1PairTerms_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R0Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R10Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R12Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R13Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R14Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R15Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R16Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R1Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R2Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R3Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R4H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R5H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R6Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R7Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R8Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1R9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I1Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2PairMassTerm_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R10Entropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R11Terms_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R1Terms_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R2H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R3H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R4Terms_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2Singleton_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/Terminal4_1_3.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Den_sound)

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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma B4_1_3Den_sound : B4_1_3Den.Encloses (((below (shape 4 1 3)).map (splitWeight positiveSecond tablep (shape 4 1 3))).sum : ℝ) := by
  sorry

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end
