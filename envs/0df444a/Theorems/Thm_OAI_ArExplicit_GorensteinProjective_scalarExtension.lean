-- Prove2me | Theorems.Thm_OAI_ArExplicit_GorensteinProjective_scalarExtension
-- name    : OAI.ArExplicit.GorensteinProjective.scalarExtension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:00:50.232882+00:00
-- url     : https://prove2.me/theorems/d45a1758-fee8-4d0b-b0db-a1c51a9aee12
-- title:
--   OAI.ArExplicit.GorensteinProjective.scalarExtension: intermediate lemma from OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ArExplicit.GorensteinProjective.scalarExtension` of [lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionComplete.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionComplete.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ArExplicit`, with `open CategoryTheory`, `open scoped TensorProduct`):
--
--   ```lean
--   theorem GorensteinProjective.scalarExtension
--       (M : Type w) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
--       (h : GorensteinProjective R M) :
--       GorensteinProjective (E ⊗[k] R) (E ⊗[k] M)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ArExplicit.GorensteinProjective` (definitions bundle `OAIQ031A019` of this split); `OAI.ArExplicit.scalarExtensionModule` (definitions bundle `OAIQ031A023` of this split).
--
--   **Used by.** The proofs of `OAI_ArExplicit_MainConclusions_scalarExtension` and `OAI.ArExplicit.Statement.fullStatement_of_mainConclusions` of this split import it.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionComplete.lean (declaration OAI.ArExplicit.GorensteinProjective.scalarExtension)

import Mathlib
import Definitions.Def_OAIQ031A019
import Definitions.Def_OAIQ031A023

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]

attribute [local instance] scalarExtensionModule

theorem GorensteinProjective.scalarExtension
    (M : Type w) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    (h : GorensteinProjective R M) :
    GorensteinProjective (E ⊗[k] R) (E ⊗[k] M) := by
  sorry

end ArExplicit

end

end OAI
end
