-- Prove2me | Theorems.Thm_OAI_Tachikawa_Construction_xTwistHom_positive
-- name    : OAI.Tachikawa.Construction.xTwistHom_positive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:56:35.016609+00:00
-- url     : https://prove2.me/theorems/fd22dfae-a8f6-4602-ba84-8d9dc7503d11
-- title:
--   OAI.Tachikawa.Construction.xTwistHom_positive: intermediate lemma from OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Tachikawa.Construction.xTwistHom_positive` of [lean/OAI/RingTheory/Tachikawa/HomProfile.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/HomProfile.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Tachikawa.Construction`, with `open CategoryTheory`, `open scoped ModuleCat.Algebra`):
--
--   ```lean
--   lemma xTwistHom_positive (n : ℕ) (x : VectorSplit.H (selfHom q) ((n+1:ℕ):ℤ)) :
--       VectorSplit.Hmap (xTwistHom q H hH) _ x = (H⁻¹)^((n+1)/3) • x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Tachikawa.VectorSplit.H`, `OAI.Tachikawa.VectorSplit.Hmap`, `OAI.Tachikawa.VectorSplit.Z` and `OAI.Tachikawa.VectorSplit.boundary` (definitions bundle `OAIQ116Ta001` of this split); `OAI.Tachikawa.Construction.selfHom` and `OAI.Tachikawa.Construction.xTwistHom` (definitions bundle `OAIQ116Ta016` of this split).
--
--   **Used by.** The proof of `OAI.Tachikawa.SourceField.sourceDelta_bijective` of this split imports it.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/HomProfile.lean (declaration OAI.Tachikawa.Construction.xTwistHom_positive)

import Mathlib
import Definitions.Def_OAIQ116Ta016

section

attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.SourceField.sourceAlgebra_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

include hq hp in
lemma xTwistHom_positive (n : ℕ) (x : VectorSplit.H (selfHom q) ((n+1:ℕ):ℤ)) :
    VectorSplit.Hmap (xTwistHom q H hH) _ x = (H⁻¹)^((n+1)/3) • x := by
  sorry

end Tachikawa.Construction

end

end OAI
end
