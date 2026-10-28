-- Prove2me | Theorems.Thm_OAI_BinPackingGap_pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082
-- name    : OAI.BinPackingGap.pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:22:28.403571+00:00
-- url     : https://prove2.me/theorems/ec4ef0f1-1ab6-4620-968a-a9633d85442b
-- title:
--   OAI.BinPackingGap.pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082: intermediate lemma from OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BinPackingGap.pEqualsNP_of_absoluteAdditiveAlgorithm` of [lean/OAI/Computability/BinPacking/Results/AdditiveHardness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Results/AdditiveHardness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BinPackingGap`):
--
--   ```lean
--   theorem pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082 (c : Nat)
--       (algorithm : AbsoluteAdditiveAlgorithm c) : PEqualsNP
--   ```
--
--   **Definitions.** The statement is written with `OAI.BinPackingGap.AbsoluteAdditiveAlgorithm` and `OAI.BinPackingGap.PEqualsNP` (the published bundle `Def_BinPackingGap`).
--
--   **Used by.** The proof of `OAI.BinPackingGap.main_results` of this split imports it.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Results/AdditiveHardness.lean (declaration OAI.BinPackingGap.pEqualsNP_of_absoluteAdditiveAlgorithm)

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

theorem pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082 (c : Nat)
    (algorithm : AbsoluteAdditiveAlgorithm c) : PEqualsNP := by
  sorry

end BinPackingGap

end OAI
end
