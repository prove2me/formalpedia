-- Prove2me | Theorems.Thm_OAI_KaplanskyConsequences_separable_extraction
-- name    : OAI.KaplanskyConsequences.separable_extraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T15:25:10.214428+00:00
-- url     : https://prove2.me/theorems/8654b9e8-0b58-4b67-a8a1-678e04b1458f
-- title:
--   OAI.KaplanskyConsequences.separable_extraction: intermediate lemma from OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KaplanskyConsequences.separable_extraction` of [lean/OAI/Analysis/Kaplansky/Kaplansky/Quotient/Extraction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Quotient/Extraction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KaplanskyConsequences`):
--
--   ```lean
--   theorem separable_extraction {A : Type} [CStarAlgebra A] [Nontrivial A]
--       (hA : StablyFinite A) (hτ : IsEmpty (TracialState A)) :
--       TraceFreeStablyFinite
--   ```
--
--   **Definitions.** The statement is written with `OAI.KaplanskyConsequences.StablyFinite`, `OAI.KaplanskyConsequences.TraceFreeStablyFinite` and `OAI.KaplanskyConsequences.TracialState` (the published bundle `Def_KaplanskyStableFiniteness`).
--
--   **Used by.** The proof of `OAI.KaplanskyConsequences.trace_free_stably_finite_exists` of this split imports it.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Quotient/Extraction.lean (declaration OAI.KaplanskyConsequences.separable_extraction)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace KaplanskyConsequences

theorem separable_extraction {A : Type} [CStarAlgebra A] [Nontrivial A]
    (hA : StablyFinite A) (hτ : IsEmpty (TracialState A)) :
    TraceFreeStablyFinite := by
  sorry

end KaplanskyConsequences
end
end

end OAI
end
