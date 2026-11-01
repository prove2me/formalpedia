-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_occupationQuadratic_rotation_integrable_s50
-- name    : OAI.Laughlin.Fock.occupationQuadratic_rotation_integrable_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:51:14.532395+00:00
-- url     : https://prove2.me/theorems/acdd7dc6-688b-4b0e-8326-1cfcdec279a8
-- title:
--   OAI.Laughlin.Fock.occupationQuadratic_rotation_integrable_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.occupationQuadratic_rotation_integrable` of [lean/OAI/Analysis/Laughlin/FourBody/HaarTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/HaarTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation Spin MeasureTheory`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem occupationQuadratic_rotation_integrable_s50 {I : Type*} [Fintype I]
--       (Q : ℕ) (R : I → I → ℝ) (L : I → Module.End ℂ (Space Q)) (x : Space Q) :
--       Integrable (fun g : SourceSU2 => occupationQuadratic Q R
--         (fun i => L i (exteriorRotation Q g⁻¹ x))) sourceHaar
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.occupationQuadratic`, `OAI.Laughlin.Rotation.sourceHaar` and `OAI.Laughlin.Rotation.sourceSU2_measurableSpace` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.exteriorRotation` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physical_fourBody_haar_transfer_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/HaarTransfer.lean (declaration OAI.Laughlin.Fock.occupationQuadratic_rotation_integrable)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Topology

theorem occupationQuadratic_rotation_integrable_s50 {I : Type*} [Fintype I]
    (Q : ℕ) (R : I → I → ℝ) (L : I → Module.End ℂ (Space Q)) (x : Space Q) :
    Integrable (fun g : SourceSU2 => occupationQuadratic Q R
      (fun i => L i (exteriorRotation Q g⁻¹ x))) sourceHaar := by
  sorry

end Laughlin.Fock

end OAI
end
