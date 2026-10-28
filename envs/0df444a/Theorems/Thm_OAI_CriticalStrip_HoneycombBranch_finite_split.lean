-- Prove2me | Theorems.Thm_OAI_CriticalStrip_HoneycombBranch_finite_split
-- name    : OAI.CriticalStrip.HoneycombBranch.finite_split
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T01:49:24.533304+00:00
-- url     : https://prove2.me/theorems/2c4b1ec1-002d-4058-8b43-66c25c685367
-- title:
--   OAI.CriticalStrip.HoneycombBranch.finite_split: intermediate lemma from OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalStrip.HoneycombBranch.finite_split` of [lean/OAI/Combinatorics/StripMass/StripMass/FluxWindow.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/FluxWindow.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalStrip.HoneycombBranch`, with `open scoped Classical BigOperators`, `open FiniteBranchTree Filter Topology`):
--
--   ```lean
--   lemma finite_split {D : Vertex→Prop} {H : ℕ} {i : ℤ}
--       (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (m : ℕ) :
--       (∑l∈physicalExits D H i m,wordWeight factor l)+
--       (∑l∈sideExits D H i m,wordWeight factor l)=1
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalStrip.FiniteBranchTree.wordWeight`, `OAI.CriticalStrip.HoneycombBranch.Vertex`, `OAI.CriticalStrip.HoneycombBranch.physicalExits` and `OAI.CriticalStrip.HoneycombBranch.sideExits` (definitions bundle `OAIQ042S001` of this split); `OAI.CriticalStrip.HoneycombBranch.factor` (definitions bundle `OAIQ042S005` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalStrip.HoneycombBranch.physical_stepped_flux` and `OAI.CriticalStrip.critical_strip_mass` of this split import it.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/FluxWindow.lean (declaration OAI.CriticalStrip.HoneycombBranch.finite_split)

import Mathlib
import Definitions.Def_OAIQ042S005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree Filter Topology

lemma finite_split {D : Vertex→Prop} {H : ℕ} {i : ℤ}
    (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (m : ℕ) :
    (∑l∈physicalExits D H i m,wordWeight factor l)+
    (∑l∈sideExits D H i m,wordWeight factor l)=1 := by
  sorry

end

end CriticalStrip.HoneycombBranch

end OAI
end
