-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_physical_pair_norm_haar_real
-- name    : OAI.Laughlin.Fock.physical_pair_norm_haar_real
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:30:50.958626+00:00
-- url     : https://prove2.me/theorems/7f7301e6-304c-401a-be22-86bb408e4d7e
-- title:
--   OAI.Laughlin.Fock.physical_pair_norm_haar_real: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.physical_pair_norm_haar_real` of [lean/OAI/Analysis/Laughlin/Fock/OrbitIntegration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/OrbitIntegration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--   theorem physical_pair_norm_haar_real (Q : ℕ) (hQ : 0 < Q) (p : Fin (2*Q-2+1)) (x : Space Q) :
--       (∫ g, occupationNormSq Q (sourcePairEnd Q p.val (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
--         sourceFockEnergy Q x/(2*Q-2+1 : ℕ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space` and `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Fock.exteriorRotation`, `OAI.Laughlin.Fock.occupationNormSq`, `OAI.Laughlin.Fock.sourceFockEnergy`, `OAI.Laughlin.Fock.sourcePairEnd`, `OAI.Laughlin.Rotation.sourceHaar` and `OAI.Laughlin.Rotation.sourceSU2_measurableSpace` (definitions bundle `OAIQ047L002` of this split).
--
--   **Used by.** The proofs of `OAI_Laughlin_Fock_physical_fourBody_haar_allowance`, `OAI_Laughlin_Fock_physical_fourBody_haar_transfer`, `OAI.Laughlin.Fock.physical_fourBody_total_haar_transfer`, `OAI_Laughlin_Fock_physical_threeBody_projector_bound`, `OAI.Laughlin.Fock.physical_threeBody_tail_sum` and `OAI.Laughlin.Fock.sourceA4Form_retained_bound` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/OrbitIntegration.lean (declaration OAI.Laughlin.Fock.physical_pair_norm_haar_real)

import Mathlib
import Definitions.Def_OAIQ047L002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators

theorem physical_pair_norm_haar_real (Q : ℕ) (hQ : 0 < Q) (p : Fin (2*Q-2+1)) (x : Space Q) :
    (∫ g, occupationNormSq Q (sourcePairEnd Q p.val (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      sourceFockEnergy Q x/(2*Q-2+1 : ℕ) := by
  sorry

end Laughlin.Fock

end OAI
end
