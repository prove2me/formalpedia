-- Prove2me | Theorems.Thm_OAI_Lech_frobeniusModule_finiteLength
-- name    : OAI.Lech.frobeniusModule_finiteLength
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:18:12.269439+00:00
-- url     : https://prove2.me/theorems/06cc8cdf-406c-4f47-8124-87d8fadf8242
-- title:
--   OAI.Lech.frobeniusModule_finiteLength: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open scoped TensorProduct`):
--
--   ```lean
--   lemma frobeniusModule_finiteLength [IsLocalRing D] [IsNoetherianRing D]
--       (hM : IsFiniteLength D M) (n : ℕ) : IsFiniteLength D (FrobeniusModule D p n M)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.FrobeniusModule` (definitions bundle `OAIQ032L004` of this split).
--
--   **Used by.** The proofs of `OAI.Lech.CharP.real_frobeniusModule_limit` and `OAI.Lech.exists_frobenius_tensor_transfer` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L004

section

attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct
universe u

variable (D : Type u) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
variable (M : ModuleCat.{u} D)

lemma frobeniusModule_finiteLength [IsLocalRing D] [IsNoetherianRing D]
    (hM : IsFiniteLength D M) (n : ℕ) : IsFiniteLength D (FrobeniusModule D p n M) := by
  sorry
end Lech

end

end OAI
end
