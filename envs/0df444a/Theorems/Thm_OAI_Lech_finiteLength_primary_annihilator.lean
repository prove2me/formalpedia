-- Prove2me | Theorems.Thm_OAI_Lech_finiteLength_primary_annihilator
-- name    : OAI.Lech.finiteLength_primary_annihilator
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:06:09.270199+00:00
-- url     : https://prove2.me/theorems/dcdb5ce9-cdcd-441d-9be0-2fabd25e52cd
-- title:
--   OAI.Lech.finiteLength_primary_annihilator: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`):
--
--   ```lean
--   lemma finiteLength_primary_annihilator (hM : IsFiniteLength D M) :
--       ∃ H : Ideal D, H.radical = IsLocalRing.maximalIdeal D ∧
--         H ≤ Module.annihilator D M
--   ```
--
--   **Used by.** The proofs of `OAI.Lech.CharP.normalized_perfection_module_finite`, `OAI.Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer`, `OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto`, `OAI.Lech.SeparableOrder.exists_normalization_frobenius_module_limit`, `OAI.Lech.exists_frobenius_tensor_transfer`, `OAI.Lech.frobeniusModule_finiteLength`, `OAI.Lech.frobenius_quotient_homology_finiteLength`, `OAI.Lech.frobenius_shortComplex_homology_finiteLength`, `OAI.Lech.shortComplex_nullScalar_radical` and `OAI.Lech.short_rank_euler_zero` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Lech
variable {D M : Type*} [CommRing D] [IsLocalRing D]
  [AddCommGroup M] [Module D M]

lemma finiteLength_primary_annihilator (hM : IsFiniteLength D M) :
    ∃ H : Ideal D, H.radical = IsLocalRing.maximalIdeal D ∧
      H ≤ Module.annihilator D M := by
  sorry
end Lech

end OAI
end
