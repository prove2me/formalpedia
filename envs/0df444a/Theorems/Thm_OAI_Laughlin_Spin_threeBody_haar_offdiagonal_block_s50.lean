-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_threeBody_haar_offdiagonal_block_s50
-- name    : OAI.Laughlin.Spin.threeBody_haar_offdiagonal_block_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T21:01:37.373211+00:00
-- url     : https://prove2.me/theorems/ac8bdb58-74a2-4892-9ea5-05de78006799
-- title:
--   OAI.Laughlin.Spin.threeBody_haar_offdiagonal_block_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.threeBody_haar_offdiagonal_block` of [lean/OAI/Analysis/Laughlin/ThreeBody/HaarBlocks.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HaarBlocks.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open scoped BigOperators Matrix Kronecker`, `open Rotation MeasureTheory`):
--
--   ```lean
--   theorem threeBody_haar_offdiagonal_block_s50 (Q : ℕ) (hQ : 2 ≤ Q) (z w : Fin (Q+1))
--       (hzw : z ≠ w) (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
--       (threeCoupledInclusion Q hQ z)ᴴ * matrixIntegral sourceHaar
--         (conjugateOrbit (threeBodySpinRepresentation Q) M) * threeCoupledInclusion Q hQ w = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.Orbital` (definitions bundle `OAIQ050L003` of this split); `OAI.Laughlin.Rotation.SourceSU2` and `OAI.Laughlin.Spin.coupledWeight` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Rotation.conjugateOrbit` and `OAI.Laughlin.Rotation.matrixIntegral` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Spin.PairOrbitalIndex` (definitions bundle `OAIQ050L011` of this split); `OAI.Laughlin.Rotation.sourceHaar` and `OAI.Laughlin.Rotation.sourceSU2_measurableSpace` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Spin.threeBodySpinRepresentation` and `OAI.Laughlin.Spin.threeCoupledInclusion` (definitions bundle `OAIQ050L021` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Spin.physical_threeBody_haar_normalization_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HaarBlocks.lean (declaration OAI.Laughlin.Spin.threeBody_haar_offdiagonal_block)

import Mathlib
import Definitions.Def_OAIQ050L021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker
open Rotation MeasureTheory

theorem threeBody_haar_offdiagonal_block_s50 (Q : ℕ) (hQ : 2 ≤ Q) (z w : Fin (Q+1))
    (hzw : z ≠ w) (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
    (threeCoupledInclusion Q hQ z)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (threeBodySpinRepresentation Q) M) * threeCoupledInclusion Q hQ w = 0 := by
  sorry

end Laughlin.Spin

end OAI
end
