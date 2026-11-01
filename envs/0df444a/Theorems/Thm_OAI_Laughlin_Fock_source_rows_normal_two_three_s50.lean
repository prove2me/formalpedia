-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_source_rows_normal_two_three_s50
-- name    : OAI.Laughlin.Fock.source_rows_normal_two_three_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T21:00:21.549419+00:00
-- url     : https://prove2.me/theorems/893cff18-5b45-406b-be00-0691b8077527
-- title:
--   OAI.Laughlin.Fock.source_rows_normal_two_three_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.source_rows_normal_two_three` of [lean/OAI/Analysis/Laughlin/FourBody/Assembly.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/Assembly.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Spin`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem source_rows_normal_two_three_s50 (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
--       (Certificate.rows.map (fun row => (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ))).sum =
--         contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
--           (physicalTwoBodyMatrix Q) x +
--         contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x +
--         (Certificate.rows.map (fun row => sourceRowFourForm Q hQ row x)).sum
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Certificate.rows` (definitions bundle `OAIQ050L001` of this split); `OAI.Laughlin.Spin.Orbital` (definitions bundle `OAIQ050L003` of this split); `OAI.Laughlin.Fock.contractionForm` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.occupationNormSq` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Spin.PairOrbitalIndex` (definitions bundle `OAIQ050L011` of this split); `OAI.Laughlin.Fock.physicalTwoBodyMatrix` and `OAI.Laughlin.Fock.sourcePairEnd` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.sourceThreeEnd` (definitions bundle `OAIQ050L017` of this split); `OAI.Laughlin.Fock.sourceRowFourForm`, `OAI.Laughlin.Fock.sourceRowSquareVector` and `OAI.Laughlin.Spin.physicalThreeBodyMatrix` (definitions bundle `OAIQ050L020` of this split); `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.source_seven_squares_normal_form_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/Assembly.lean (declaration OAI.Laughlin.Fock.source_rows_normal_two_three)

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
open Spin
open scoped BigOperators Matrix

theorem source_rows_normal_two_three_s50 (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
    (Certificate.rows.map (fun row => (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ))).sum =
      contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
        (physicalTwoBodyMatrix Q) x +
      contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x +
      (Certificate.rows.map (fun row => sourceRowFourForm Q hQ row x)).sum := by
  sorry

end Laughlin.Fock

end OAI
end
