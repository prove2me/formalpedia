-- Prove2me | Theorems.Thm_OAI_BinPackingGap_InventoryData_long_matches_at_nonexcluded_oaiq082
-- name    : OAI.BinPackingGap.InventoryData.long_matches_at_nonexcluded_oaiq082
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T14:02:51.334618+00:00
-- url     : https://prove2.me/theorems/8fc78ee8-86fd-41de-ace6-5dfe17364c0e
-- title:
--   OAI.BinPackingGap.InventoryData.long_matches_at_nonexcluded_oaiq082: intermediate lemma from OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BinPackingGap.InventoryData.long_matches_at_nonexcluded` of [lean/OAI/Computability/BinPacking/Configurations/CoverageSoundness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Configurations/CoverageSoundness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BinPackingGap.InventoryData`):
--
--   ```lean
--   theorem long_matches_at_nonexcluded_oaiq082 {b c : ℕ}
--       (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
--       (hL : 1 ≤ D.L) (hk : D.k ≤ D.graph.n)
--       (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
--       (v : D.Vertex) (r : D.IncidencePosition v)
--       (hr : D.incidencePosition r ∉ PackingCounts.excludedAt p D.itemEquiv v) :
--       D.d ≤ D.longMatchesAt p v r + PackingCounts.xplus p D.itemEquiv v + 9 * lossAllowance c
--   ```
--
--   **Definitions.** The statement is written with `OAI.BinPackingGap.UniformTree` (definitions bundle `OAIQ082C002` of this split); `OAI.BinPackingGap.lossAllowance` and `OAI.BinPackingGap.GraphInput` (definitions bundle `OAIQ082C003` of this split); `OAI.BinPackingGap.InventoryData`, `OAI.BinPackingGap.InventoryData.B`, `OAI.BinPackingGap.InventoryData.Position`, `OAI.BinPackingGap.InventoryData.Vertex`, `OAI.BinPackingGap.InventoryData.itemEquiv` and `OAI.BinPackingGap.InventoryData.packingInstance` (definitions bundle `OAIQ082C008` of this split); `OAI.BinPackingGap.InventoryData.IncidencePosition` and `OAI.BinPackingGap.InventoryData.incidencePosition` (definitions bundle `OAIQ082C014` of this split); `OAI.BinPackingGap.PackingCounts.excludedAt` and `OAI.BinPackingGap.PackingCounts.xplus` (definitions bundle `OAIQ082C015` of this split); `OAI.BinPackingGap.InventoryData.longMatchesAt` (definitions bundle `OAIQ082C021` of this split); `OAI.BinPackingGap.Packing` (the published bundle `Def_BinPackingGap`).
--
--   **Used by.** The proofs of `OAI.BinPackingGap.PCPFoundation.packingOutput_sound_oaiq082` and `OAI.BinPackingGap.main_results` of this split import it.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Configurations/CoverageSoundness.lean (declaration OAI.BinPackingGap.InventoryData.long_matches_at_nonexcluded)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C021

section

attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeDescriptor _root_.OAI.BinPackingGap.PackingCoordinateExpression.instFintypeTreeDescriptor _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

namespace InventoryData

variable (D : InventoryData)

theorem long_matches_at_nonexcluded_oaiq082 {b c : ℕ}
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (v : D.Vertex) (r : D.IncidencePosition v)
    (hr : D.incidencePosition r ∉ PackingCounts.excludedAt p D.itemEquiv v) :
    D.d ≤ D.longMatchesAt p v r + PackingCounts.xplus p D.itemEquiv v + 9 * lossAllowance c := by
  sorry

end InventoryData
end BinPackingGap

end

end OAI
end
