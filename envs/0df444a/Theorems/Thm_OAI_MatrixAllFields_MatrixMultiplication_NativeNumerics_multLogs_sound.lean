-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_multLogs_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.multLogs_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T15:20:28.034205+00:00
-- url     : https://prove2.me/theorems/2acd44e7-ec36-4c6e-b7e3-4953d387da68
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.multLogs_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.multLogs_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate AllFieldNativeCapacity`, `open scoped BigOperators`):
--
--   ```lean
--   lemma multLogs_sound (a : PairSlot) :
--       (multLogs a).Encloses (Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.PairSlot` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.multiplicity` (definitions bundle `OAIQ254M001` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.multLogs` (definitions bundle `OAIQ254M011` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_7_1Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_8_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_0_7Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z1_7_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_0_6Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z2_6_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_0_5Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z3_5_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_0_4Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z4_4_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_0_3Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z5_3_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z6_0_2Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z6_2_0Four_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z7_0_1Four_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z8_0_0Four_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.multLogs_sound)

import Mathlib
import Definitions.Def_OAIQ254M011

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
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma multLogs_sound (a : PairSlot) :
    (multLogs a).Encloses (Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  sorry

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end
