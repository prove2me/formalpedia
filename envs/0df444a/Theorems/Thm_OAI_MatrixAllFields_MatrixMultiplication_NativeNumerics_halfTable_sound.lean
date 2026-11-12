-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_halfTable_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:55:03.901169+00:00
-- url     : https://prove2.me/theorems/6add5733-809f-467a-a0bf-f158053c800f
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/SupportedContraction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SupportedContraction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate AllFieldNativeCapacity`, `open scoped BigOperators`):
--
--   ```lean
--   lemma halfTable_sound (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3) (ij : PairSlot) :
--       (halfTable t w ij).Encloses (halfLaw t w ij : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.PairSlot`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.halfLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.shapes` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable` (definitions bundle `OAIQ254M007` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_1_14I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_2_13I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_3_12I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1ResidualEntropies_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1Group_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1ResidualEntropies_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.capacityABalls_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SupportedContraction.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable_sound)

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
lemma halfTable_sound (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3) (ij : PairSlot) :
    (halfTable t w ij).Encloses (halfLaw t w ij : ℝ) := by
  sorry

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end
