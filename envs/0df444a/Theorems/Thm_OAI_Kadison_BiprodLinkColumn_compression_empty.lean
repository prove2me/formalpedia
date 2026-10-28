-- Prove2me | Theorems.Thm_OAI_Kadison_BiprodLinkColumn_compression_empty
-- name    : OAI.Kadison.BiprodLinkColumn.compression_empty
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:22.646202+00:00
-- url     : https://prove2.me/theorems/faa36e7e-8510-42c3-b6f7-e440349ae97e
-- title:
--   OAI.Kadison.BiprodLinkColumn.compression_empty: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.BiprodLinkColumn`, with `open HilbertBiprod PartialIsometryOrder`):
--
--   ```lean
--   lemma compression_empty : compression N S ∅=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertBiprod.Space` (definitions bundle `OAIQ039C000` of this split); `OAI.Kadison.BiprodLinkColumn.Intertwiner` and `OAI.Kadison.BiprodLinkColumn.compression` (definitions bundle `OAIQ039C020` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.NormalRepresentation.separable_traced_factor_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C020

section

attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (N : VonNeumannAlgebra (Space H G)) (S : Set (Intertwiner N))

lemma compression_empty : compression N S ∅=0 := by
  sorry

end Kadison.BiprodLinkColumn

end

end
end

end OAI
end
