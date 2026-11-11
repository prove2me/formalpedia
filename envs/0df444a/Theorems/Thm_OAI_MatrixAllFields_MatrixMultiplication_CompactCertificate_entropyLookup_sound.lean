-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.entropyLookup_sound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-11T05:56:44.600233+00:00
-- url     : https://prove2.me/theorems/595a935f-3a39-4fcf-82d4-19acf070402d
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.entropyLookup_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.entropyLookup_sound` of [lean/OAI/LinearAlgebra/MatrixFields/Entropy/ZeroLeafRateFormula.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/ZeroLeafRateFormula.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldCertificates AllFieldCertificates.Replay`):
--
--   ```lean
--   lemma entropyLookup_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
--       {cs : List EntropyDatum} (h : cs.all (fun c => c.check two) = true)
--       (i : ℕ) {x : ℝ} (hx : (entropyLookup cs i).input.Encloses x) :
--       (entropyLookup cs i).output.Encloses (Foundation.entropyTerm x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball`, `OAI.MatrixAllFields.MatrixMultiplication.Foundation.entropyTerm` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.EntropyDatum`, `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.entropyLookup`, `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.EntropyDatum.check`, `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.EntropyDatum.input` and `OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.EntropyDatum.output` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proofs of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_4_11I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_2_12I0_sound`, `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I0_sound` and `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I0_sound` of this split import it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/ZeroLeafRateFormula.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.entropyLookup_sound)

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

namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay

lemma entropyLookup_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {cs : List EntropyDatum} (h : cs.all (fun c => c.check two) = true)
    (i : ℕ) {x : ℝ} (hx : (entropyLookup cs i).input.Encloses x) :
    (entropyLookup cs i).output.Encloses (Foundation.entropyTerm x) := by
  sorry

end MatrixMultiplication.CompactCertificate

end MatrixAllFields

end OAI
end
