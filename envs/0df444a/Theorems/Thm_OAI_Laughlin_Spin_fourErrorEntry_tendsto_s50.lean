-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_fourErrorEntry_tendsto_s50
-- name    : OAI.Laughlin.Spin.fourErrorEntry_tendsto_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T20:46:09.0932+00:00
-- url     : https://prove2.me/theorems/16512653-087a-49c6-9981-afdbe9a7c17f
-- title:
--   OAI.Laughlin.Spin.fourErrorEntry_tendsto_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.fourErrorEntry_tendsto` of [lean/OAI/Analysis/Laughlin/FourBody/ErrorLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/ErrorLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open scoped Topology`, `open Filter`):
--
--   ```lean
--   theorem fourErrorEntry_tendsto_s50 (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
--       (hr : r ≤ D) (hs : s ≤ D) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1) :
--       Tendsto (fun Q => fourErrorEntry Q D r s t e f) atTop (𝓝 (fourErrorLimitEntry D r s t e f))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.fourErrorLimitEntry` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Spin.fourErrorEntry` (definitions bundle `OAIQ050L010` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.finiteLocalFourMatrix_tendsto_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/ErrorLimit.lean (declaration OAI.Laughlin.Spin.fourErrorEntry_tendsto)

import Mathlib
import Definitions.Def_OAIQ050L010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem fourErrorEntry_tendsto_s50 (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (hr : r ≤ D) (hs : s ≤ D) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1) :
    Tendsto (fun Q => fourErrorEntry Q D r s t e f) atTop (𝓝 (fourErrorLimitEntry D r s t e f)) := by
  sorry

end Laughlin.Spin

end OAI
end
