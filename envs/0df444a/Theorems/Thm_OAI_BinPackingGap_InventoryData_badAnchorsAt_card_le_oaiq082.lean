-- Prove2me | Theorems.Thm_OAI_BinPackingGap_InventoryData_badAnchorsAt_card_le_oaiq082
-- name    : OAI.BinPackingGap.InventoryData.badAnchorsAt_card_le_oaiq082
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:46:56.586331+00:00
-- url     : https://prove2.me/theorems/8a880db0-c02c-4fdb-83e8-f321c7c5fc46
-- title:
--   OAI.BinPackingGap.InventoryData.badAnchorsAt_card_le_oaiq082: intermediate lemma from OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BinPackingGap.InventoryData.badAnchorsAt_card_le` of [lean/OAI/Computability/BinPacking/Inventory/InventoryPrefixConservation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/InventoryPrefixConservation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BinPackingGap.InventoryData`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem badAnchorsAt_card_le_oaiq082 {b c : ℕ} (hk : D.k ≤ D.graph.n)
--       (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (v : D.Vertex) :
--       (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel v).card ≤
--         3 * lossAllowance c
--   ```
--
--   **Definitions.** The statement is written with `OAI.BinPackingGap.lossAllowance` and `OAI.BinPackingGap.GraphInput` (definitions bundle `OAIQ082C003` of this split); `OAI.BinPackingGap.InventoryData`, `OAI.BinPackingGap.Coverage.badAnchorsAt`, `OAI.BinPackingGap.InventoryData.B`, `OAI.BinPackingGap.InventoryData.Vertex` and `OAI.BinPackingGap.InventoryData.packingInstance` (definitions bundle `OAIQ082C008` of this split); `OAI.BinPackingGap.InventoryData.encodedLabel` and `OAI.BinPackingGap.InventoryData.encodedSubclass` (definitions bundle `OAIQ082C015` of this split); `OAI.BinPackingGap.Packing` and `OAI.BinPackingGap.Instance.Item` (the published bundle `Def_BinPackingGap`).
--
--   **Used by.** The proofs of `OAI.BinPackingGap.InventoryData.long_matches_at_nonexcluded_oaiq082` and `OAI.BinPackingGap.extractedCover_card_le_oaiq082` of this split import it.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/InventoryPrefixConservation.lean (declaration OAI.BinPackingGap.InventoryData.badAnchorsAt_card_le)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

namespace InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem badAnchorsAt_card_le_oaiq082 {b c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (v : D.Vertex) :
    (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel v).card ≤
      3 * lossAllowance c := by
  sorry

end InventoryData
end BinPackingGap

end

end OAI
end
