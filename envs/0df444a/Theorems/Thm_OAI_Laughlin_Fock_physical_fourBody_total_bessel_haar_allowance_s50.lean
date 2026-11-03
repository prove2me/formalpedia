-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_physical_fourBody_total_bessel_haar_allowance_s50
-- name    : OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:52:27.910761+00:00
-- url     : https://prove2.me/theorems/56df1add-bda7-49b2-8ba9-df8a52666159
-- title:
--   OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance` of [lean/OAI/Analysis/Laughlin/FourBody/BesselAllowance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/BesselAllowance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Spin Rotation MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--   theorem physical_fourBody_total_bessel_haar_allowance_s50 (Q : ℕ) (hQ : 25 ≤ Q)
--       (x : Space Q) :
--       (∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1),
--         (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
--           (physicalFourCopyEnd Q (oddPairDeficit r) (d.val+1)
--             (by have := oddPairDeficit_le r; omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)) ≤
--         1222 * sourceFockEnergy Q x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Rotation.SourceSU2` and `OAI.Laughlin.Spin.OddPairLabel` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.occupationNormSq` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.sourceFockEnergy`, `OAI.Laughlin.Rotation.sourceHaar`, `OAI.Laughlin.Rotation.sourceSU2_measurableSpace`, `OAI.Laughlin.Spin.oddPairDeficit` and `OAI.Laughlin.Spin.oddPairDeficit_le` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.exteriorRotation` and `OAI.Laughlin.Fock.physicalFourCopyEnd` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.sourceA4Form_retained_bessel_bound_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/BesselAllowance.lean (declaration OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance)

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
open Spin Rotation MeasureTheory
open scoped BigOperators

theorem physical_fourBody_total_bessel_haar_allowance_s50 (Q : ℕ) (hQ : 25 ≤ Q)
    (x : Space Q) :
    (∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1),
      (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
        (physicalFourCopyEnd Q (oddPairDeficit r) (d.val+1)
          (by have := oddPairDeficit_le r; omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)) ≤
      1222 * sourceFockEnergy Q x := by
  sorry

end Laughlin.Fock

end OAI
end
