-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourceThreeHighestEnd_haar_s50
-- name    : OAI.Laughlin.Fock.sourceThreeHighestEnd_haar_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:54:25.224498+00:00
-- url     : https://prove2.me/theorems/716a7ca9-f488-42dd-bec0-5c031de94d33
-- title:
--   OAI.Laughlin.Fock.sourceThreeHighestEnd_haar_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourceThreeHighestEnd_haar` of [lean/OAI/Analysis/Laughlin/ThreeBody/HighestFock.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HighestFock.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation Spin MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem sourceThreeHighestEnd_haar_s50 (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (x : Space Q) :
--       (coupledWeight Q z.val+1 : ℕ) * (∫ g, occupationNormSq Q
--         (sourceThreeHighestEnd Q z.val hQ (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
--         (contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q hQ z).map Complex.ofReal) x).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.Orbital` (definitions bundle `OAIQ050L003` of this split); `OAI.Laughlin.Fock.contractionForm`, `OAI.Laughlin.Rotation.SourceSU2` and `OAI.Laughlin.Spin.coupledWeight` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.occupationNormSq` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Spin.PairOrbitalIndex` (definitions bundle `OAIQ050L011` of this split); `OAI.Laughlin.Rotation.sourceHaar` and `OAI.Laughlin.Rotation.sourceSU2_measurableSpace` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.exteriorRotation` and `OAI.Laughlin.Spin.threeSpinProjector` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.sourceThreeEnd` and `OAI.Laughlin.Fock.sourceThreeHighestEnd` (definitions bundle `OAIQ050L017` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.physical_threeBody_projector_bound_s50` and `OAI.Laughlin.Fock.physical_threeBody_projector_nonneg_s50` of this split import it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HighestFock.lean (declaration OAI.Laughlin.Fock.sourceThreeHighestEnd_haar)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem sourceThreeHighestEnd_haar_s50 (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (x : Space Q) :
    (coupledWeight Q z.val+1 : ℕ) * (∫ g, occupationNormSq Q
      (sourceThreeHighestEnd Q z.val hQ (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      (contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q hQ z).map Complex.ofReal) x).re := by
  sorry

end Laughlin.Fock

end OAI
end
