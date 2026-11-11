-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_roundedMarginal_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T05:53:47.313769+00:00
-- url     : https://prove2.me/theorems/cebd219f-4cc9-437d-9cc3-dce7c9491d4f
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay`, `open scoped BigOperators`):
--
--   ```lean
--   lemma roundedMarginal_sound (k : Fin 17) :
--       (roundedMarginal k).Encloses (AllFieldInitialEntropy.nativeInitialMarginal k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.nativeInitialMarginal` (definitions bundle `OAIQ254M002` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.nativeH0_enclosed` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound)

import Mathlib
import Definitions.Def_OAIQ254M002
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

lemma roundedMarginal_sound (k : Fin 17) :
    (roundedMarginal k).Encloses (AllFieldInitialEntropy.nativeInitialMarginal k) := by
  sorry

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

end OAI
end
