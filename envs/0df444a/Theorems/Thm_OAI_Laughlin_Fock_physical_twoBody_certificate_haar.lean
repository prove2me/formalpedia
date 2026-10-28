-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_physical_twoBody_certificate_haar
-- name    : OAI.Laughlin.Fock.physical_twoBody_certificate_haar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:32:07.353389+00:00
-- url     : https://prove2.me/theorems/f906c5d4-ca17-48a8-97cb-56fae4cd62f1
-- title:
--   OAI.Laughlin.Fock.physical_twoBody_certificate_haar: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.physical_twoBody_certificate_haar` of [lean/OAI/Analysis/Laughlin/Spin/TwoBodyCertificateHaar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/TwoBodyCertificateHaar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Rotation MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem physical_twoBody_certificate_haar (Q : ℕ) (hQ : 5 ≤ Q) (x : Space Q) :
--       ((2*Q-2+1 : ℕ) : ℂ) * (∫ g, contractionForm Q
--         (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) (physicalTwoBodyMatrix Q)
--         (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
--         (93527408868499/10^14 : ℂ) * (sourceFockEnergy Q x : ℂ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space`, `OAI.Laughlin.Fock.contractionForm` and `OAI.Laughlin.Rotation.SourceSU2` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Fock.exteriorRotation`, `OAI.Laughlin.Fock.physicalTwoBodyMatrix`, `OAI.Laughlin.Fock.sourceFockEnergy`, `OAI.Laughlin.Fock.sourcePairEnd`, `OAI.Laughlin.Rotation.sourceHaar` and `OAI.Laughlin.Rotation.sourceSU2_measurableSpace` (definitions bundle `OAIQ047L002` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.sourceKForm_decomposition` of this split imports it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/TwoBodyCertificateHaar.lean (declaration OAI.Laughlin.Fock.physical_twoBody_certificate_haar)

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
open scoped BigOperators Matrix

theorem physical_twoBody_certificate_haar (Q : ℕ) (hQ : 5 ≤ Q) (x : Space Q) :
    ((2*Q-2+1 : ℕ) : ℂ) * (∫ g, contractionForm Q
      (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) (physicalTwoBodyMatrix Q)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      (93527408868499/10^14 : ℂ) * (sourceFockEnergy Q x : ℂ) := by
  sorry

end Laughlin.Fock

end OAI
end
