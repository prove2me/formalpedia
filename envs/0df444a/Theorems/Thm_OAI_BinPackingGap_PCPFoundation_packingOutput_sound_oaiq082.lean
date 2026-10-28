-- Prove2me | Theorems.Thm_OAI_BinPackingGap_PCPFoundation_packingOutput_sound_oaiq082
-- name    : OAI.BinPackingGap.PCPFoundation.packingOutput_sound_oaiq082
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T14:02:07.771874+00:00
-- url     : https://prove2.me/theorems/3b1053c4-1d57-4b0d-a1b0-278d6cf1f39a
-- title:
--   OAI.BinPackingGap.PCPFoundation.packingOutput_sound_oaiq082: intermediate lemma from OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BinPackingGap.PCPFoundation.packingOutput_sound` of [lean/OAI/Computability/BinPacking/Hardness/PCPPackingGap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Hardness/PCPPackingGap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BinPackingGap.PCPFoundation`, with `open BinPackingGames.Foundations.Target`):
--
--   ```lean
--   theorem packingOutput_sound_oaiq082 (c : Nat) (F : Formula) (hF : ¬ F.Satisfiable) :
--       ¬ HasPacking ((packingOutput c F).2.toInstance (packingOutput_valid c F))
--         ((packingOutput c F).1 + c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BinPackingGames.Foundations.Target.Formula` (definitions bundle `OAIQ082C000` of this split); `OAI.BinPackingGames.Foundations.Target.Formula.Satisfiable` (definitions bundle `OAIQ082C006` of this split); `OAI.BinPackingGap.PCPFoundation.packingOutput` and `OAI.BinPackingGap.PCPFoundation.packingOutput_valid` (definitions bundle `OAIQ082C021` of this split); `OAI.BinPackingGap.HasPacking`, `OAI.BinPackingGap.RawInstance` and `OAI.BinPackingGap.RawInstance.toInstance` (the published bundle `Def_BinPackingGap`).
--
--   **Used by.** The proof of `OAI.BinPackingGap.packingGapNPHard_oaiq082` of this split imports it.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Hardness/PCPPackingGap.lean (declaration OAI.BinPackingGap.PCPFoundation.packingOutput_sound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PCPFoundation

open BinPackingGames.Foundations.Target

theorem packingOutput_sound_oaiq082 (c : Nat) (F : Formula) (hF : ¬ F.Satisfiable) :
    ¬ HasPacking ((packingOutput c F).2.toInstance (packingOutput_valid c F))
      ((packingOutput c F).1 + c) := by
  sorry

end BinPackingGap.PCPFoundation

end

end OAI
end
