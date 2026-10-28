-- Prove2me | Theorems.Thm_OAI_CriticalStrip_Diagram_physical_augmented_stationary
-- name    : OAI.CriticalStrip.Diagram.physical_augmented_stationary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T02:14:49.055477+00:00
-- url     : https://prove2.me/theorems/51ce2443-398a-476d-a10d-416152a16f72
-- title:
--   OAI.CriticalStrip.Diagram.physical_augmented_stationary: intermediate lemma from OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalStrip.Diagram.physical_augmented_stationary` of [lean/OAI/Combinatorics/StripMass/StripMass/NorthMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/NorthMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalStrip.Diagram`, with `open scoped Classical BigOperators`, `open _root_.Matrix Filter Topology`):
--
--   ```lean
--   lemma physical_augmented_stationary (N : ℕ) :
--       (restrictedColumn (SewnRectangle.leftWeights N)).mulVec
--           (fun p=>angleAugmented (fun _ : Fin N=>lambda) p.val)+
--         injectionColumn (SewnRectangle.leftWeights N)=
--         fun p=>angleAugmented (fun _ : Fin N=>lambda) p.val
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalStrip.Diagram.NonemptyPairing`, `OAI.CriticalStrip.Diagram.Pairing`, `OAI.CriticalStrip.Diagram.empty`, `OAI.CriticalStrip.Diagram.instDecidableEqPairing`, `OAI.CriticalStrip.Diagram.instFintypePairing` and `OAI.CriticalStrip.Diagram.lambda` (definitions bundle `OAIQ042S000` of this split); `OAI.CriticalStrip.Diagram.injectionColumn`, `OAI.CriticalStrip.Diagram.restrictedColumn` and `OAI.CriticalStrip.SewnRectangle.leftWeights` (definitions bundle `OAIQ042S002` of this split); `OAI.CriticalStrip.Diagram.angleAugmented` (definitions bundle `OAIQ042S015` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalStrip.HoneycombBranch.physical_stepped_flux` and `OAI.CriticalStrip.critical_strip_mass` of this split import it.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/NorthMass.lean (declaration OAI.CriticalStrip.Diagram.physical_augmented_stationary)

import Mathlib
import Definitions.Def_OAIQ042S015

section

attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators
open _root_.Matrix Filter Topology

lemma physical_augmented_stationary (N : ℕ) :
    (restrictedColumn (SewnRectangle.leftWeights N)).mulVec
        (fun p=>angleAugmented (fun _ : Fin N=>lambda) p.val)+
      injectionColumn (SewnRectangle.leftWeights N)=
      fun p=>angleAugmented (fun _ : Fin N=>lambda) p.val := by
  sorry

end
end CriticalStrip.Diagram

end OAI
end
