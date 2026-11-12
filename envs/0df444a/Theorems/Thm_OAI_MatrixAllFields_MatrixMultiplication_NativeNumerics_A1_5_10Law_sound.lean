-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A1_5_10Law_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_5_10Law_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:13:45.55347+00:00
-- url     : https://prove2.me/theorems/7f155d41-cd3c-4ea3-ad6e-cd5590ba1d79
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_5_10Law_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_5_10Law_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB1_3_4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB1_3_4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate`, `open scoped BigOperators`):
--
--   ```lean
--   lemma A1_5_10Law_sound (u : Shape) :
--       (A1_5_10Law u).Encloses (stageALaw (shape 1 5 10) u : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.stageALaw` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_5_10Law` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1PairH_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R0H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R10H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R11H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R12Entropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R13Entropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R14Terms_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R15Terms_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R1H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R2H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R3H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R4H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R5H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R6H_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R7Raw_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R8Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1R9Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1Singleton_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I1_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairEntropy_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2PairMassTerm_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2Singleton_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_5_10I2_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/SplitB1_3_4.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A1_5_10Law_sound)

import Mathlib
import Definitions.Def_OAIQ254M003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A1_5_10Law_sound (u : Shape) :
    (A1_5_10Law u).Encloses (stageALaw (shape 1 5 10) u : ℝ) := by
  sorry

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end
