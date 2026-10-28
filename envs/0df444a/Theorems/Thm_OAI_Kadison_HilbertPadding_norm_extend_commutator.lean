-- Prove2me | Theorems.Thm_OAI_Kadison_HilbertPadding_norm_extend_commutator
-- name    : OAI.Kadison.HilbertPadding.norm_extend_commutator
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:35:20.410545+00:00
-- url     : https://prove2.me/theorems/2ff68fd6-6fd9-4719-8783-8af26e3b8639
-- title:
--   OAI.Kadison.HilbertPadding.norm_extend_commutator: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.HilbertPadding`, with `open scoped BigOperators InnerProductSpace`, `open ContinuousLinearMap`):
--
--   ```lean
--   lemma norm_extend_commutator (E : H →ₗᵢ[ℂ] K) (T a : H →L[ℂ] H) (b : K →L[ℂ] K)
--       (hl : b.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp a)
--       (hr : E.toContinuousLinearMap.adjoint.comp b=a.comp E.toContinuousLinearMap.adjoint) :
--       ‖extend E T*b-b*extend E T‖=‖T*a-a*T‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertPadding.extend` (definitions bundle `OAIQ039C012` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.HilbertPadding.amplified_extension_commutator_norm`, `OAI.Kadison.HilbertPadding.doubleCopies_commutator_norm` and `OAI.Kadison.HilbertPadding.rightCopies_commutator_norm` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_extend_commutator (E : H →ₗᵢ[ℂ] K) (T a : H →L[ℂ] H) (b : K →L[ℂ] K)
    (hl : b.comp E.toContinuousLinearMap=E.toContinuousLinearMap.comp a)
    (hr : E.toContinuousLinearMap.adjoint.comp b=a.comp E.toContinuousLinearMap.adjoint) :
    ‖extend E T*b-b*extend E T‖=‖T*a-a*T‖ := by
  sorry

end Kadison.HilbertPadding

end

end
end

end OAI
end
