-- Prove2me | Theorems.Thm_OAI_Tachikawa_SourceField_sourceDelta_bijective
-- name    : OAI.Tachikawa.SourceField.sourceDelta_bijective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:54:54.6123+00:00
-- url     : https://prove2.me/theorems/8fcf80d6-4bfd-462c-9fc3-8edde43326dd
-- title:
--   OAI.Tachikawa.SourceField.sourceDelta_bijective: intermediate lemma from OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Tachikawa.SourceField.sourceDelta_bijective` of [lean/OAI/RingTheory/Tachikawa/Delta.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Delta.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Tachikawa.SourceField`, with `open Construction`):
--
--   ```lean
--   lemma sourceDelta_bijective (a : ℤ) (ha : 0 < a ∨ a ≤ -3) :
--       Function.Bijective (sourceDelta a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Tachikawa.VectorSplit.H`, `OAI.Tachikawa.VectorSplit.Z` and `OAI.Tachikawa.VectorSplit.boundary` (definitions bundle `OAIQ116Ta001` of this split); `OAI.Tachikawa.SourceField.Base`, `OAI.Tachikawa.SourceField.H₁`, `OAI.Tachikawa.SourceField.H₂`, `OAI.Tachikawa.SourceField.K`, `OAI.Tachikawa.SourceField.one_add_q_pow_ne_zero`, `OAI.Tachikawa.SourceField.parameter_ne_zero` and `OAI.Tachikawa.SourceField.q` (definitions bundle `OAIQ116Ta002` of this split); `OAI.Tachikawa.Construction.FHom`, `OAI.Tachikawa.Construction.selfHom` and `OAI.Tachikawa.SourceField.sourceDelta` (definitions bundle `OAIQ116Ta016` of this split).
--
--   **Used by.** The proof of `OAI.Tachikawa.SourceField.sourceCone_closed_boundary` of this split imports it.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Delta.lean (declaration OAI.Tachikawa.SourceField.sourceDelta_bijective)

import Mathlib
import Definitions.Def_OAIQ116Ta016

section

attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Tachikawa

namespace SourceField
open Construction

lemma sourceDelta_bijective (a : ℤ) (ha : 0 < a ∨ a ≤ -3) :
    Function.Bijective (sourceDelta a) := by
  sorry

end SourceField
end Tachikawa

end

end OAI
end
