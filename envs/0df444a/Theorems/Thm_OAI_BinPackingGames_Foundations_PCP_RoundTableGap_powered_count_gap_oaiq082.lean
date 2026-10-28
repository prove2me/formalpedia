-- Prove2me | Theorems.Thm_OAI_BinPackingGames_Foundations_PCP_RoundTableGap_powered_count_gap_oaiq082
-- name    : OAI.BinPackingGames.Foundations.PCP.RoundTableGap.powered_count_gap_oaiq082
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:56:37.467074+00:00
-- url     : https://prove2.me/theorems/51255b6e-d0bc-4bc8-b384-896b6d797439
-- title:
--   OAI.BinPackingGames.Foundations.PCP.RoundTableGap.powered_count_gap_oaiq082: intermediate lemma from OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BinPackingGames.Foundations.PCP.RoundTableGap.powered_count_gap` of [lean/OAI/Computability/BinPacking/PCP/RoundTableGap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/PCP/RoundTableGap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BinPackingGames.Foundations.PCP.RoundTableGap`, with `open RoundTables`, `open PoweringWalks SpectralReturn`):
--
--   ```lean
--   theorem powered_count_gap_oaiq082 (input : Input)
--       (labeling : Fin (powered H input.val).vertices → Fin alphabet) :
--       RoundGap.poweredLower (gap input) * ((powered H input.val).darts : ℝ) ≤
--         ((GenericGraphTables.semantics (powered H input.val)).rejectionCount labeling : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BinPackingGames.Foundations.PCP.ConstraintGraph.rejectionCount`, `OAI.BinPackingGames.Foundations.PCP.ExpanderTables.graph` and `OAI.BinPackingGames.Foundations.PCP.GraphTables.Table` (definitions bundle `OAIQ082C000` of this split); `OAI.BinPackingGames.Foundations.PCP.Expanders.baseDegree`, `OAI.BinPackingGames.Foundations.PCP.GenericGraphTables.Label` and `OAI.BinPackingGames.Foundations.PCP.GenericGraphTables.Table` (definitions bundle `OAIQ082C001` of this split); `OAI.BinPackingGames.Foundations.PCP.GenericGraphTables.semantics`, `OAI.BinPackingGames.Foundations.PCP.RoundTables.BaseTable` and `OAI.BinPackingGames.Foundations.PCP.SpectralReturn.SpectralCertificate` (definitions bundle `OAIQ082C005` of this split); `OAI.BinPackingGames.Foundations.PCP.RoundGap.poweredLower` (definitions bundle `OAIQ082C007` of this split); `OAI.BinPackingGames.Foundations.PCP.RoundTables.Input`, `OAI.BinPackingGames.Foundations.PCP.RoundTables.alphabet` and `OAI.BinPackingGames.Foundations.PCP.RoundTables.powered` (definitions bundle `OAIQ082C010` of this split); `OAI.BinPackingGames.Foundations.PCP.RoundTables.gap` (definitions bundle `OAIQ082C020` of this split).
--
--   **Used by.** The proofs of `OAI.BinPackingGap.PCPFoundation.packingOutput_sound_oaiq082` and `OAI.BinPackingGap.packingGapNPHard_oaiq082` of this split import it.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/PCP/RoundTableGap.lean (declaration OAI.BinPackingGames.Foundations.PCP.RoundTableGap.powered_count_gap)

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_OAIQ082C020

section

attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype _root_.OAI.BinPackingGap.UniformTree.nodeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RoundTableGap

open RoundTables
open PoweringWalks SpectralReturn

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem powered_count_gap_oaiq082 (input : Input)
    (labeling : Fin (powered H input.val).vertices → Fin alphabet) :
    RoundGap.poweredLower (gap input) * ((powered H input.val).darts : ℝ) ≤
      ((GenericGraphTables.semantics (powered H input.val)).rejectionCount labeling : ℝ) := by
  sorry

end BinPackingGames.Foundations.PCP.RoundTableGap

end OAI
end
