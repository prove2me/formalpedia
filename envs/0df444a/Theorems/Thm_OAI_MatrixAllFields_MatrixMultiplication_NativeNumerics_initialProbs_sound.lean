-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_initialProbs_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:43:32.578815+00:00
-- url     : https://prove2.me/theorems/06b8888e-79ad-4168-8274-e3b38134c268
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Certificates/InitialProbabilities.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/InitialProbabilities.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate`, `open scoped BigOperators`):
--
--   ```lean
--   lemma initialProbs_sound (g : Shape) (hg : g ∈ sortedInitial) :
--       (initialProbs g).Encloses (initialLaw g : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.initialLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.sortedInitial` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs` (definitions bundle `OAIQ254M005` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_1_6U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_3_4U0_0_4Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3Masses_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_1_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_0_3Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_4_3U1_3_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_2_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_3_1Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U0_4_0Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B1_5_2U1_1_2Mass_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B2_5_1S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2Btotal_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B5_1_2S2_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1Btotal_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.B6_1_1S2_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Certificates/InitialProbabilities.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.initialProbs_sound)

import Mathlib
import Definitions.Def_OAIQ254M005

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
lemma initialProbs_sound (g : Shape) (hg : g ∈ sortedInitial) :
    (initialProbs g).Encloses (initialLaw g : ℝ) := by
  sorry

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end
