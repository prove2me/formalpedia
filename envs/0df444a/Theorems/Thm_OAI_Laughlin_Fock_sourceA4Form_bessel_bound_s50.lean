-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourceA4Form_bessel_bound_s50
-- name    : OAI.Laughlin.Fock.sourceA4Form_bessel_bound_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:58:47.827676+00:00
-- url     : https://prove2.me/theorems/915f9607-8350-4d23-b062-28d4a116762e
-- title:
--   OAI.Laughlin.Fock.sourceA4Form_bessel_bound_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourceA4Form_bessel_bound` of [lean/OAI/Analysis/Laughlin/FourBody/BesselAllowance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/BesselAllowance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Spin Rotation MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--   theorem sourceA4Form_bessel_bound_s50 (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
--       sourceA4Form Q x ≤
--         (∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
--           occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))) +
--         (1222*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.occupationNormSq` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.sourceFockEnergy` and `OAI.Laughlin.Fock.sourcePairEnd` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.averagedFourTransferError` (definitions bundle `OAIQ050L016` of this split); `OAI.Laughlin.Fock.sourceA4Form` (definitions bundle `OAIQ050L020` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physical_fock_sharp_budget_eventually_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/BesselAllowance.lean (declaration OAI.Laughlin.Fock.sourceA4Form_bessel_bound)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators

theorem sourceA4Form_bessel_bound_s50 (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x ≤
      (∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))) +
      (1222*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x := by
  sorry

end Laughlin.Fock

end OAI
end
