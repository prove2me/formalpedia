-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_2_3I1ResidualEntropies_sound
-- name    : OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1ResidualEntropies_sound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T13:35:16.167368+00:00
-- url     : https://prove2.me/theorems/88874234-9b6d-46ac-a34a-eafb81affed4
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1ResidualEntropies_sound: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1ResidualEntropies_sound` of [lean/OAI/LinearAlgebra/MatrixFields/CapacityB/CapB3_2_3I1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/CapacityB/CapB3_2_3I1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay`, `open AllFieldInitialEntropyCertificate AllFieldNativeCapacity`, `open scoped BigOperators`):
--
--   ```lean
--   lemma CB3_2_3I1ResidualEntropies_sound (k : Fin 17) :
--       (CB3_2_3I1ResidualEntropies k).Encloses (homogeneousEntropy
--         (residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) k))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.stageBPriority`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.residualLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.below`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.homogeneousEntropy`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.littleLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.stageBLaw` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Ball.Encloses` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1ResidualEntropies` (definitions bundle `OAIQ254M004` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1_sound` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/CapacityB/CapB3_2_3I1.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_2_3I1ResidualEntropies_sound)

import Mathlib
import Definitions.Def_OAIQ254M004

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
lemma CB3_2_3I1ResidualEntropies_sound (k : Fin 17) :
    (CB3_2_3I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) k)) := by
  sorry

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end
