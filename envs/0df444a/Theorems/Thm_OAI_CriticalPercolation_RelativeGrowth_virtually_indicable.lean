-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_RelativeGrowth_virtually_indicable
-- name    : OAI.CriticalPercolation.RelativeGrowth.virtually_indicable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:22:42.534792+00:00
-- url     : https://prove2.me/theorems/d86cb224-a515-4be1-a1d0-a0b813dd83bc
-- title:
--   OAI.CriticalPercolation.RelativeGrowth.virtually_indicable: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.RelativeGrowth.virtually_indicable` of [lean/OAI/Probability/CriticalPercolation/Growth/CosetIndicability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Growth/CosetIndicability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.RelativeGrowth`, with `open Set Function`, `open scoped Classical Pointwise`):
--
--   ```lean
--   lemma virtually_indicable {K : Subgroup A} {S : Set A} {d : ℕ}
--       (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
--       (hK : Bounded S (K:Set A)) (hg : HasDegree K S d) [Infinite (A ⧸ K)] :
--       ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
--         Surjective q ∧ K.subgroupOf H≤q.ker
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.RelativeGrowth.Bounded` and `OAI.CriticalPercolation.RelativeGrowth.HasDegree` (definitions bundle `OAIQ228B001` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Growth/CosetIndicability.lean (declaration OAI.CriticalPercolation.RelativeGrowth.virtually_indicable)

import Mathlib
import Definitions.Def_OAIQ228B001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A B : Type*} [Group A] [Group B]

lemma virtually_indicable {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hg : HasDegree K S d) [Infinite (A ⧸ K)] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
      Surjective q ∧ K.subgroupOf H≤q.ker := by
  sorry

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end
