-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_B3_2_3Raw_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Raw_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:20:28.256218+00:00
-- url     : https://prove2.me/theorems/886d3990-935f-49fe-9932-96bc35ee058f
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Raw_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Raw_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB5_1_2.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB5_1_2.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate`, `open scoped BigOperators`):
--
--   ```lean
--   lemma B3_2_3Raw_sound (u : Shape) (hu : u ∈ below (shape 3 2 3)) :
--       (B3_2_3Raw u).Encloses (splitWeight positiveSecond tablep (shape 3 2 3) u : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.below`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.positiveSecond`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.splitWeight`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.tablep` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Raw` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Den_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R0Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R10Entropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R10Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R11P_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R12Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R13Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R14Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R15Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R16Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R1MassTerm_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R1Terms_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R2H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R3H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R4H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R5Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R6Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R7Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R8Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1R9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2R0H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2R10H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2R1H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2R2H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2R3H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2R4H_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I2_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB5_1_2.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Raw_sound)

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
lemma B3_2_3Raw_sound (u : Shape) (hu : u ∈ below (shape 3 2 3)) :
    (B3_2_3Raw u).Encloses (splitWeight positiveSecond tablep (shape 3 2 3) u : ℝ) := by
  sorry

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end
