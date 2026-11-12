-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_nonnegative_radius
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.nonnegative_radius
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:11:43.72947+00:00
-- url     : https://prove2.me/theorems/9b0b47b6-0c6f-4a61-9033-3ff29ecbc69c
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.nonnegative_radius: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.nonnegative_radius` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, with `open scoped BigOperators Topology Polynomial`):
--
--   ```lean
--   theorem nonnegative_radius {b : Ball} {x : ℝ} (h : b.Encloses x) : 0 ≤ b.radius
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.mul_sound` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.nonnegative_radius)

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

namespace Ball

theorem nonnegative_radius {b : Ball} {x : ℝ} (h : b.Encloses x) : 0 ≤ b.radius := by
  sorry

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end
