-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_threeCoupledInclusion_adjoint_SU2_s50
-- name    : OAI.Laughlin.Spin.threeCoupledInclusion_adjoint_SU2_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T21:01:58.9369+00:00
-- url     : https://prove2.me/theorems/68e10c71-460b-436e-8adc-1621e3b10069
-- title:
--   OAI.Laughlin.Spin.threeCoupledInclusion_adjoint_SU2_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.threeCoupledInclusion_adjoint_SU2` of [lean/OAI/Analysis/Laughlin/ThreeBody/HaarBlocks.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HaarBlocks.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open scoped BigOperators Matrix Kronecker`, `open Rotation MeasureTheory`):
--
--   ```lean
--   theorem threeCoupledInclusion_adjoint_SU2_s50 (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
--       (g : SourceSU2) :
--       (threeCoupledInclusion Q hQ z)ᴴ * threeBodySpinRepresentation Q g =
--         sourceSpinRepresentation (coupledWeight Q z.val) g * (threeCoupledInclusion Q hQ z)ᴴ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.Orbital` (definitions bundle `OAIQ050L003` of this split); `OAI.Laughlin.Rotation.SourceSU2` and `OAI.Laughlin.Spin.coupledWeight` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Spin.PairOrbitalIndex` (definitions bundle `OAIQ050L011` of this split); `OAI.Laughlin.Rotation.sourceSpinRepresentation` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Spin.threeBodySpinRepresentation` and `OAI.Laughlin.Spin.threeCoupledInclusion` (definitions bundle `OAIQ050L021` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Spin.threeBody_haar_diagonal_block_s50` and `OAI.Laughlin.Spin.threeBody_haar_offdiagonal_block_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HaarBlocks.lean (declaration OAI.Laughlin.Spin.threeCoupledInclusion_adjoint_SU2)

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

theorem threeCoupledInclusion_adjoint_SU2_s50 (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (g : SourceSU2) :
    (threeCoupledInclusion Q hQ z)ᴴ * threeBodySpinRepresentation Q g =
      sourceSpinRepresentation (coupledWeight Q z.val) g * (threeCoupledInclusion Q hQ z)ᴴ := by
  sorry

end Laughlin.Spin

end OAI
end
