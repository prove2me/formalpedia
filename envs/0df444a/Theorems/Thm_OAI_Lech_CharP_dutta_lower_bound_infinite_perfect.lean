-- Prove2me | Theorems.Thm_OAI_Lech_CharP_dutta_lower_bound_infinite_perfect
-- name    : OAI.Lech.CharP.dutta_lower_bound_infinite_perfect
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:45:24.284121+00:00
-- url     : https://prove2.me/theorems/23b3ea46-a6c5-4b4c-a196-1f02d9bdf293
-- title:
--   OAI.Lech.CharP.dutta_lower_bound_infinite_perfect: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.CharP`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing`, `open scoped Topology`):
--
--   ```lean
--   theorem dutta_lower_bound_infinite_perfect (hd : 0 < dimension D)
--       (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsShortComplex D F) :
--       multiplicity D ≤ duttaMultiplicity D p F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.IsShortComplex`, `OAI.Lech.dimension`, `OAI.Lech.duttaMultiplicity` and `OAI.Lech.multiplicity` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.dutta_algClosed` of this split imports it.
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
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]
  [Infinite (ResidueField D)]

theorem dutta_lower_bound_infinite_perfect (hd : 0 < dimension D)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsShortComplex D F) :
    multiplicity D ≤ duttaMultiplicity D p F := by
  sorry
end Lech.CharP

end

end OAI
end
