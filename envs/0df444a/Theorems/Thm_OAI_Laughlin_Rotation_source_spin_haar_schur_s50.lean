-- Prove2me | Theorems.Thm_OAI_Laughlin_Rotation_source_spin_haar_schur_s50
-- name    : OAI.Laughlin.Rotation.source_spin_haar_schur_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:56:32.47046+00:00
-- url     : https://prove2.me/theorems/d8af1b81-7d39-4eb9-8e47-eafc068225bc
-- title:
--   OAI.Laughlin.Rotation.source_spin_haar_schur_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Rotation.source_spin_haar_schur` of [lean/OAI/Analysis/Laughlin/Spin/Schur.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Schur.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Rotation`, with `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem source_spin_haar_schur_s50 (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :
--       matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M) =
--         (Matrix.trace M / (Q+1 : ℕ)) • (1 : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Rotation.conjugateOrbit` and `OAI.Laughlin.Rotation.matrixIntegral` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Rotation.sourceHaar` and `OAI.Laughlin.Rotation.sourceSU2_measurableSpace` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Rotation.sourceSpinRepresentation` (definitions bundle `OAIQ050L016` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.physical_pair_norm_haar_real_s50`, `OAI.Laughlin.Fock.physical_twoBody_certificate_haar_s50`, `OAI.Laughlin.Rotation.embedded_spin_haar_s50`, `OAI.Laughlin.Spin.fourBody_cross_orbit_s50`, `OAI.Laughlin.Spin.physical_fourBody_haar_multiplicity_s50` and `OAI.Laughlin.Spin.threeBody_haar_diagonal_block_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Schur.lean (declaration OAI.Laughlin.Rotation.source_spin_haar_schur)

import Mathlib
import Definitions.Def_OAIQ050L016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

theorem source_spin_haar_schur_s50 (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M) =
      (Matrix.trace M / (Q+1 : ℕ)) • (1 : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) := by
  sorry

end Laughlin.Rotation

end OAI
end
