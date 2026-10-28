-- Prove2me | Theorems.Thm_OAI_CriticalStrip_HoneycombBranch_strip_turn
-- name    : OAI.CriticalStrip.HoneycombBranch.strip_turn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T01:31:26.221221+00:00
-- url     : https://prove2.me/theorems/c4d3c215-60ec-42fa-be49-168387115393
-- title:
--   OAI.CriticalStrip.HoneycombBranch.strip_turn: intermediate lemma from OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalStrip.HoneycombBranch.strip_turn` of [lean/OAI/Combinatorics/StripMass/StripMass/PhysicalPorts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/PhysicalPorts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalStrip.HoneycombBranch`, with `open scoped Classical BigOperators`, `open FiniteBranchTree`):
--
--   ```lean
--   lemma strip_turn (H : ℕ) (hH : 1≤H) (i : ℤ) (x : ExitWord (bandVertices H) i) :
--       turn x.val=stripTurn i (exitPort (stripBoundaryPorts H hH) x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalStrip.HoneycombBranch.ExitWord`, `OAI.CriticalStrip.HoneycombBranch.IsExit`, `OAI.CriticalStrip.HoneycombBranch.bandVertices`, `OAI.CriticalStrip.HoneycombBranch.exitPort`, `OAI.CriticalStrip.HoneycombBranch.stripBoundaryPorts`, `OAI.CriticalStrip.HoneycombBranch.stripTurn` and `OAI.CriticalStrip.HoneycombBranch.turn` (definitions bundle `OAIQ042S001` of this split).
--
--   **Used by.** The proof of `OAI.CriticalStrip.critical_strip_mass` of this split imports it.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/PhysicalPorts.lean (declaration OAI.CriticalStrip.HoneycombBranch.strip_turn)

import Mathlib
import Definitions.Def_OAIQ042S001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

variable {D : Vertex→Prop} {B : Type*} (P : BoundaryPorts D B) {H : ℕ} {i : ℤ}

lemma strip_turn (H : ℕ) (hH : 1≤H) (i : ℤ) (x : ExitWord (bandVertices H) i) :
    turn x.val=stripTurn i (exitPort (stripBoundaryPorts H hH) x) := by
  sorry

end

end CriticalStrip.HoneycombBranch

end OAI
end
