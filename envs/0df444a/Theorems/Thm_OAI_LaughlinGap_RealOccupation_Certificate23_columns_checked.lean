-- Prove2me | Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate23_columns_checked
-- name    : OAI.LaughlinGap.RealOccupation.Certificate23.columns_checked
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T03:19:28.006155+00:00
-- url     : https://prove2.me/theorems/12fe6c77-0482-43ae-af7a-f5450a867b82
-- title:
--   OAI.LaughlinGap.RealOccupation.Certificate23.columns_checked: intermediate lemma from OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LaughlinGap.RealOccupation.Certificate23.columns_checked` of [lean/OAI/Analysis/LaughlinGap/Certificate23.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate23.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LaughlinGap.RealOccupation.Certificate23`, with `open scoped BigOperators ComplexOrder`, `open Spin`):
--
--   ```lean
--   lemma columns_checked : ∀ u : Fin 12, ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns u v
--   ```
--
--   **Definitions.** The statement is written with `OAI.LaughlinGap.Occupation.wordSign` and `OAI.LaughlinGap.RealOccupation.FourTerm` (definitions bundle `OAIQ030L000` of this split); `OAI.LaughlinGap.RealOccupation.Certificate23.columns` (definitions bundle `OAIQ030L014` of this split); `OAI.LaughlinGap.RealOccupation.fourTermLabels` (definitions bundle `OAIQ030L028` of this split); `OAI.LaughlinGap.RealOccupation.Certificate23.fibers` (definitions bundle `OAIQ030L033` of this split); `OAI.LaughlinGap.RealOccupation.fourTermEval` (definitions bundle `OAIQ030L035` of this split).
--
--   **Used by.** The proof of `OAI.LaughlinGap.RealOccupation.Certificate23.certificate` of this split imports it.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate23.lean (declaration OAI.LaughlinGap.RealOccupation.Certificate23.columns_checked)

import Mathlib
import Definitions.Def_OAIQ030L033
import Definitions.Def_OAIQ030L035

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate23

lemma columns_checked : ∀ u : Fin 12, ∀ v : Fin 84, (∑ b ∈ fibers v, fourTermEval 23 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 23 ≤ 23) b)) = columns u v := by
  sorry
end Certificate23
end LaughlinGap.RealOccupation

end

end OAI
end
