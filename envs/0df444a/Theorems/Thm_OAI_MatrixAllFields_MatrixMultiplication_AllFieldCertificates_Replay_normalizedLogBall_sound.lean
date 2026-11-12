-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_normalizedLogBall_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T05:48:29.703906+00:00
-- url     : https://prove2.me/theorems/4b2a5cba-c3f1-454b-9c5a-34b6aa7fc3aa
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay`, with `open scoped BigOperators Topology Polynomial`):
--
--   ```lean
--   theorem normalizedLogBall_sound {m : ℚ} {trace : List Ball}
--       (hlo : 1 ≤ m) (hhi : m ≤ 2)
--       (hc : checkPolynomial (.exact (logVariable m ^ 2)) logCoefficients trace = true) :
--       (normalizedLogBall m trace).Encloses (Real.log (m : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.exact`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.logCoefficients`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.logVariable` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall` (definitions bundle `OAIQ254M000` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U0_2_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U0_2_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_0_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_0_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_2_0ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_2_0EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U0_2_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U0_2_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_0_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_0_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_2_0ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_2_0EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I0_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I0_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound)

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
namespace MatrixMultiplication.AllFieldCertificates.Replay

theorem normalizedLogBall_sound {m : ℚ} {trace : List Ball}
    (hlo : 1 ≤ m) (hhi : m ≤ 2)
    (hc : checkPolynomial (.exact (logVariable m ^ 2)) logCoefficients trace = true) :
    (normalizedLogBall m trace).Encloses (Real.log (m : ℝ)) := by
  sorry

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end
