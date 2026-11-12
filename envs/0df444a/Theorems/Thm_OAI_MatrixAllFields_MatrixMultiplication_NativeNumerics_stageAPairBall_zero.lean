-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_stageAPairBall_zero
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.stageAPairBall_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T15:23:53.887195+00:00
-- url     : https://prove2.me/theorems/771879a2-0d46-4996-b1c7-442c2b6d6cb5
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.stageAPairBall_zero: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.stageAPairBall_zero` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/SupportedContraction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SupportedContraction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate AllFieldNativeCapacity`, `open scoped BigOperators`):
--
--   ```lean
--   lemma stageAPairBall_zero (s : Shape) (hs : s ∈ positiveInitial) (bs : Shape → Ball)
--       (w : Fin 3) (ij : PairSlot × PairSlot)
--       (h : pairDegree ij.1 + pairDegree ij.2 ≠ s w) :
--       sparsePairLawBall (below s) s bs (fun u => halfTable u w) ij = .exact 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.PairSlot`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.below`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.positiveInitial` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.exact` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.sparsePairLawBall` (definitions bundle `OAIQ254M003` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.halfTable` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.pairDegree` (definitions bundle `OAIQ254M007` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairMassTerm_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2PairP_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1PairRaw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I1PairP_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_7_7I2PairP_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_3_10I2PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_4_9I2PairP_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_5_8I2PairP_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I1PairP_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA3_6_7I2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_4_8I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_5_7I2PairP_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I1PairP_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA4_6_6I2PairP_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA5_5_6I2PairP_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.stageAPairBall_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SupportedContraction.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.stageAPairBall_zero)

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

lemma stageAPairBall_zero (s : Shape) (hs : s ∈ positiveInitial) (bs : Shape → Ball)
    (w : Fin 3) (ij : PairSlot × PairSlot)
    (h : pairDegree ij.1 + pairDegree ij.2 ≠ s w) :
    sparsePairLawBall (below s) s bs (fun u => halfTable u w) ij = .exact 0 := by
  sorry

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end
