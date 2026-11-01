-- Prove2me | Theorems.Thm_OAI_Laughlin_Rotation_source_unequal_spin_haar_zero_s50
-- name    : OAI.Laughlin.Rotation.source_unequal_spin_haar_zero_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:56:56.306027+00:00
-- url     : https://prove2.me/theorems/b7998f59-fbcc-433d-8aae-3c8e29c6d6e6
-- title:
--   OAI.Laughlin.Rotation.source_unequal_spin_haar_zero_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Rotation.source_unequal_spin_haar_zero` of [lean/OAI/Analysis/Laughlin/Spin/HaarOrthogonality.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/HaarOrthogonality.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Rotation`, with `open scoped Matrix`):
--
--   ```lean
--   theorem source_unequal_spin_haar_zero_s50 (m n : ℕ) (hmn : m ≠ n)
--       (M : Matrix (Fin (m+1)) (Fin (n+1)) ℂ) :
--       rectangularIntegral sourceHaar
--         (rectangularOrbit (sourceSpinRepresentation m) (sourceSpinRepresentation n) M)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Rotation.rectangularIntegral` and `OAI.Laughlin.Rotation.rectangularOrbit` (definitions bundle `OAIQ050L008` of this split); `OAI.Laughlin.Rotation.sourceHaar` and `OAI.Laughlin.Rotation.sourceSU2_measurableSpace` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Rotation.sourceSpinRepresentation` (definitions bundle `OAIQ050L016` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Spin.fourBody_haar_unequal_spin_s50` and `OAI.Laughlin.Spin.threeBody_haar_offdiagonal_block_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/HaarOrthogonality.lean (declaration OAI.Laughlin.Rotation.source_unequal_spin_haar_zero)

import Mathlib
import Definitions.Def_OAIQ050L008
import Definitions.Def_OAIQ050L016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped Matrix

theorem source_unequal_spin_haar_zero_s50 (m n : ℕ) (hmn : m ≠ n)
    (M : Matrix (Fin (m+1)) (Fin (n+1)) ℂ) :
    rectangularIntegral sourceHaar
      (rectangularOrbit (sourceSpinRepresentation m) (sourceSpinRepresentation n) M)=0 := by
  sorry

end Laughlin.Rotation

end OAI
end
