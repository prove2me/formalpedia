-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_log_center_lipschitz
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.log_center_lipschitz
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T05:48:38.046199+00:00
-- url     : https://prove2.me/theorems/88e13588-997d-4b3b-a6d2-5fc2a24f19ad
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.log_center_lipschitz: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.log_center_lipschitz` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates`, with `open scoped BigOperators Topology Polynomial`):
--
--   ```lean
--   theorem log_center_lipschitz {b : Ball} {x : ℝ} (hx : b.Encloses x)
--       (hpos : 0 < b.lower) :
--       |Real.log x - Real.log (b.center : ℝ)| ≤ (b.radius / b.lower : ℚ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.lower` (definitions bundle `OAIQ254M000` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.checkLog_sound` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.log_center_lipschitz)

import Mathlib
import Definitions.Def_OAIQ254M000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates

theorem log_center_lipschitz {b : Ball} {x : ℝ} (hx : b.Encloses x)
    (hpos : 0 < b.lower) :
    |Real.log x - Real.log (b.center : ℝ)| ≤ (b.radius / b.lower : ℚ) := by
  sorry

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end
