-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_4_10I2PairP_check_0_0
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check_0_0
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T15:29:36.748194+00:00
-- url     : https://prove2.me/theorems/ab5c6842-1b06-4b5c-94d1-71ff21ca1728
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check_0_0: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check_0_0` of [lean/OAI/LinearAlgebra/MatrixFields/CapacityA/CapA2_4_10I2Pair.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/CapacityA/CapA2_4_10I2Pair.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate AllFieldNativeCapacity`, `open scoped BigOperators`):
--
--   ```lean
--   lemma CA2_4_10I2PairP_check_0_0 : ∀ k l : Fin 6, contains (CA2_4_10I2PairRaw ((0,0),(k,l))) (CA2_4_10I2PairP ((0,0),(k,l))) = true
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.PairSlot` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.contains` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP` (definitions bundle `OAIQ254M008` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairRaw` (definitions bundle `OAIQ254M012` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/CapacityA/CapA2_4_10I2Pair.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2PairP_check_0_0)

import Mathlib
import Definitions.Def_OAIQ254M012

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
lemma CA2_4_10I2PairP_check_0_0 : ∀ k l : Fin 6, contains (CA2_4_10I2PairRaw ((0,0),(k,l))) (CA2_4_10I2PairP ((0,0),(k,l))) = true := by
  sorry

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end
