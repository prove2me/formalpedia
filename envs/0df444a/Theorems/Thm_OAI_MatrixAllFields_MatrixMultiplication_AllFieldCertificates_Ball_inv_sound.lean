-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_inv_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.inv_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:06.309172+00:00
-- url     : https://prove2.me/theorems/ca494998-2cf5-4f8f-b71f-3b41ab8c4be0
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.inv_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.inv_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, with `open scoped BigOperators Topology Polynomial`):
--
--   ```lean
--   theorem inv_sound {a : Ball} {x : ℝ} (hx : a.Encloses x)
--       (hpos : 0 < a.lower) : (inv a).Encloses x⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.inv` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.lower` (definitions bundle `OAIQ254M000` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_1_4Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_2_3Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_4_1Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B4_1_3Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R0P_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R10H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R11H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R12H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R13H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R14H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R15H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R16H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R1H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R2Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R3H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R4H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R5H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R6Entropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R6MassTerm_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R7Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R8Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R9Raw_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1Singleton_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.inv_sound)

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

theorem inv_sound {a : Ball} {x : ℝ} (hx : a.Encloses x)
    (hpos : 0 < a.lower) : (inv a).Encloses x⁻¹ := by
  sorry

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end
