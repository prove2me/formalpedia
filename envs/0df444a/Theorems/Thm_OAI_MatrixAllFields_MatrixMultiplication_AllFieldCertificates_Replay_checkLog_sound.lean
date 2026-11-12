-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkLog_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T05:52:26.065896+00:00
-- url     : https://prove2.me/theorems/8feeaf63-9c6f-4f7d-a2d9-cd2ff935a924
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkLog_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkLog_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay`, with `open scoped BigOperators Topology Polynomial`):
--
--   ```lean
--   theorem checkLog_sound {two a b : Ball} {w : LogWitness} {x : ℝ}
--       (htwo : two.Encloses (Real.log 2)) (hx : a.Encloses x)
--       (h : checkLog two a b w = true) : b.Encloses (Real.log x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.LogWitness` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkLog` (definitions bundle `OAIQ254M002` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.nativeH0_enclosed`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_3_3Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U0_2_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U0_2_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_0_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_0_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_2_0ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_4_2U2_2_0EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U0_2_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U0_2_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_1_2Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U1_2_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_0_2ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_0_2EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_1_1Leaf_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_2_0ED_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B3_3_2U2_2_0EOneD_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I0_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I0_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/CertificatesReplay.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkLog_sound)

import Mathlib
import Definitions.Def_OAIQ254M002

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

theorem checkLog_sound {two a b : Ball} {w : LogWitness} {x : ℝ}
    (htwo : two.Encloses (Real.log 2)) (hx : a.Encloses x)
    (h : checkLog two a b w = true) : b.Encloses (Real.log x) := by
  sorry

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end
