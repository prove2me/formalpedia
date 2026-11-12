-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_5_10I2PairP_check
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairP_check
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:34:04.255298+00:00
-- url     : https://prove2.me/theorems/598f645f-3a08-416e-b208-7f5878dc09a5
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairP_check: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairP_check` of [lean/OAI/LinearAlgebra/MatrixFields/CapacityA/CapA1_5_10I2Pair.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/CapacityA/CapA1_5_10I2Pair.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate AllFieldNativeCapacity`, `open scoped BigOperators`):
--
--   ```lean
--   lemma CA1_5_10I2PairP_check (a : PairSlot × PairSlot) : contains (CA1_5_10I2PairRaw a) (CA1_5_10I2PairP a) = true
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.PairSlot` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.contains` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairP` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairRaw` (definitions bundle `OAIQ254M007` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairEntropy_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairMassTerm_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/CapacityA/CapA1_5_10I2Pair.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairP_check)

import Mathlib
import Definitions.Def_OAIQ254M007

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
lemma CA1_5_10I2PairP_check (a : PairSlot × PairSlot) : contains (CA1_5_10I2PairRaw a) (CA1_5_10I2PairP a) = true := by
  sorry

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end
