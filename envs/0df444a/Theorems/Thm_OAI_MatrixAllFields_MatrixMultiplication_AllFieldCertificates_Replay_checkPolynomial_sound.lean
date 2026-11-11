-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkPolynomial_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T05:48:39.667+00:00
-- url     : https://prove2.me/theorems/81726764-d99b-43a1-afaa-8502d435a612
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay`, with `open scoped BigOperators Topology Polynomial`, `open MatrixMultiplication.Foundation.RationalLogCertificate`):
--
--   ```lean
--   theorem checkPolynomial_sound {t : Ball} {x : ℝ} (hx : t.Encloses x)
--       (as : List ℚ) (trace : List Ball)
--       (h : checkPolynomial t as trace = true) :
--       (traceHead trace).Encloses (polynomial x as)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.traceHead` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.polynomial` (definitions bundle `OAIQ254M001` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_4_11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_6_9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_7_8Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_3_11Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Law_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Btotal_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1S2_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial_sound)

import Mathlib
import Definitions.Def_OAIQ254M000
import Definitions.Def_OAIQ254M001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

theorem checkPolynomial_sound {t : Ball} {x : ℝ} (hx : t.Encloses x)
    (as : List ℚ) (trace : List Ball)
    (h : checkPolynomial t as trace = true) :
    (traceHead trace).Encloses (polynomial x as) := by
  sorry

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end
