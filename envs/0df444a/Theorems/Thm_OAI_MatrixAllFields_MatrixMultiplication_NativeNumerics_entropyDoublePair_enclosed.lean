-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyDoublePair_enclosed
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.entropyDoublePair_enclosed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T15:20:12.74099+00:00
-- url     : https://prove2.me/theorems/113786c9-b0fe-41ba-baed-6eabfcd68c9c
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.entropyDoublePair_enclosed: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.entropyDoublePair_enclosed` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate AllFieldNativeCapacity`, `open scoped BigOperators`):
--
--   ```lean
--   lemma entropyDoublePair_enclosed (p : PairSlot × PairSlot → ℝ)
--       (bs : PairSlot × PairSlot → Ball)
--       (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
--       (doublePairSumBall bs).Encloses (Foundation.finiteEntropy p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.PairSlot`, `OAI.MatrixAllFields.MatrixMultiplication.Foundation.entropyTerm`, `OAI.MatrixAllFields.MatrixMultiplication.Foundation.finiteEntropy` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.doublePairSumBall` (definitions bundle `OAIQ254M011` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I1PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_4_10I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2PairH_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SparseContraction.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.entropyDoublePair_enclosed)

import Mathlib
import Definitions.Def_OAIQ254M011

section

attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

lemma entropyDoublePair_enclosed (p : PairSlot × PairSlot → ℝ)
    (bs : PairSlot × PairSlot → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (doublePairSumBall bs).Encloses (Foundation.finiteEntropy p) := by
  sorry

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end
