-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_RelativeGrowth_virtually_indicable_bs
-- name    : OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:31:38.059013+00:00
-- url     : https://prove2.me/theorems/3e7aa3c0-6b9f-4bb4-ab1f-11b4a9f16edd
-- title:
--   OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.RelativeGrowth.virtually_indicable` of [lean/OAI/Probability/CriticalPercolation/Growth/CosetIndicability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Growth/CosetIndicability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.RelativeGrowth`, with `open Set Function`, `open scoped Classical Pointwise`):
--
--   ```lean
--   lemma virtually_indicable_bs {K : Subgroup A} {S : Set A} {d : ℕ}
--       (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
--       (hK : Bounded S (K:Set A)) (hg : HasDegree K S d) [Infinite (A ⧸ K)] :
--       ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
--         Surjective q ∧ K.subgroupOf H≤q.ker
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.RelativeGrowth.Bounded` and `OAI.CriticalPercolation.RelativeGrowth.HasDegree` (definitions bundle `OAIQ078B001` of this split).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_finite_general_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Growth/CosetIndicability.lean (declaration OAI.CriticalPercolation.RelativeGrowth.virtually_indicable)

import Mathlib
import Definitions.Def_OAIQ078B001

section

attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

lemma virtually_indicable_bs {K : Subgroup A} {S : Set A} {d : ℕ}
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
