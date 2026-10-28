-- Prove2me | Theorems.Thm_OAI_Lech_dutta_algClosed
-- name    : OAI.Lech.dutta_algClosed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:05:37.532059+00:00
-- url     : https://prove2.me/theorems/404ab9cf-fb9f-40c2-aca9-68e2200fcf63
-- title:
--   OAI.Lech.dutta_algClosed: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing`, `open scoped Topology`):
--
--   ```lean
--   lemma dutta_algClosed (p : ℕ) [Fact p.Prime] [CharP R p]
--       (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F) :
--       Tendsto (duttaSequence R p F) atTop (𝓝 (duttaMultiplicity R p F)) ∧
--         multiplicity R ≤ duttaMultiplicity R p F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.IsShortComplex`, `OAI.Lech.duttaMultiplicity`, `OAI.Lech.duttaSequence` and `OAI.Lech.multiplicity` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.dutta_domain` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]

lemma dutta_algClosed (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F) :
    Tendsto (duttaSequence R p F) atTop (𝓝 (duttaMultiplicity R p F)) ∧
      multiplicity R ≤ duttaMultiplicity R p F := by
  sorry
end Lech

end

end OAI
end
