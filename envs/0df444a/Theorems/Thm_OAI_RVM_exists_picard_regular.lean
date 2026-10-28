-- Prove2me | Theorems.Thm_OAI_RVM_exists_picard_regular
-- name    : OAI.RVM.exists_picard_regular
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:24:28.835145+00:00
-- url     : https://prove2.me/theorems/0e646633-25a9-4c4e-86ed-5e2c8dd36a26
-- title:
--   OAI.RVM.exists_picard_regular: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.exists_picard_regular` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem exists_picard_regular {d : Datum} (hd : Admissible d) {E B : Field}
--       (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
--       ∃ s : Solution, PicardRegular d s ∧ TransportFor s E B
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.PicardRegular` and `OAI.RVM.TransportFor` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Field`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.exists_picard_field_limit` and `OAI.RVM.family_picard_field_limit` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/PicardBounds.lean (declaration OAI.RVM.exists_picard_regular)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

theorem exists_picard_regular {d : Datum} (hd : Admissible d) {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ∃ s : Solution, PicardRegular d s ∧ TransportFor s E B := by
  sorry

end RVM

end

end OAI
end
