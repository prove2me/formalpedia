-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_NInterval_mul_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.mul_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:12:03.788731+00:00
-- url     : https://prove2.me/theorems/1c96d2e5-1088-417d-bb82-96bdc0cc07bb
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.mul_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.mul_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval`, with `open scoped BigOperators Topology Polynomial`):
--
--   ```lean
--   lemma mul_sound {S : ℕ} (hS : 0 < S) {a b : NInterval} {x y : ℝ}
--       (hx : Encloses S a x) (hy : Encloses S b y) :
--       Encloses S (mul S a b) (x * y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval` and `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.mul` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.Encloses` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.oddHorner_sound` and `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.logApprox_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.NInterval.mul_sound)

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

namespace MatrixMultiplication.CompactCertificate

namespace NInterval

lemma mul_sound {S : ℕ} (hS : 0 < S) {a b : NInterval} {x y : ℝ}
    (hx : Encloses S a x) (hy : Encloses S b y) :
    Encloses S (mul S a b) (x * y) := by
  sorry

end NInterval
end MatrixMultiplication.CompactCertificate

end

end MatrixAllFields

end OAI
end
