-- Prove2me | Theorems.Thm_OAI_MatroidProphet_MainAlgorithm_listedTransferGap_parity_expectation_le
-- name    : OAI.MatroidProphet.MainAlgorithm.listedTransferGap_parity_expectation_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:28:22.266449+00:00
-- url     : https://prove2.me/theorems/7f0625a4-c2e1-4126-bd66-bb78ba48a6b0
-- title:
--   OAI.MatroidProphet.MainAlgorithm.listedTransferGap_parity_expectation_le: intermediate lemma from OpenAI, One-sample matroid prophet inequalities against an almighty adversary
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatroidProphet.Assigned.secretary`, `OAI.MatroidProphet.Assigned.one_sample` and `OAI.MatroidProphet.Assigned.hidden_vector`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *One-sample matroid prophet inequalities against an almighty adversary*, OpenAI Math Release, September 23, 2026, result family 111, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatroidProphet.MainAlgorithm.listedTransferGap_parity_expectation_le` of [lean/OAI/Probability/MatroidProphet/Residual/Global.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/MatroidProphet/Residual/Global.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatroidProphet.MainAlgorithm`, with `open Finset`):
--
--   ```lean
--   lemma listedTransferGap_parity_expectation_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
--       (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
--       (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
--       (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) :
--       tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
--         univ (fun A B C => fairParityExpectation (fun p =>
--           listedTransferGap M hE (2^100) (withMasks d A B C) s i Y (boolParity p))) ≤
--         2 * residualDelta * (trueGroup M d s i).card
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatroidProphet.MainMasks`, `OAI.MatroidProphet.boolParity`, `OAI.MatroidProphet.densityThreshold`, `OAI.MatroidProphet.fairParityExpectation`, `OAI.MatroidProphet.residualDelta`, `OAI.MatroidProphet.thinningRate`, `OAI.MatroidProphet.tripleMaskExpectation`, `OAI.MatroidProphet.MainAlgorithm.listedTransferGap`, `OAI.MatroidProphet.MainAlgorithm.trueGroup` and `OAI.MatroidProphet.MainAlgorithm.withMasks` (definitions bundle `OAIW2MS000` of this split).
--
--   **Used by.** The proof of `OAI.MatroidProphet.MainAlgorithm.conditional_main_payoff` of this split imports it.
-- source:
--   OpenAI, One-sample matroid prophet inequalities against an almighty adversary, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 111; paper: https://github.com/openai/math; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/MatroidProphet/Residual/Global.lean (declaration OAI.MatroidProphet.MainAlgorithm.listedTransferGap_parity_expectation_le)

import Mathlib
import Definitions.Def_OAIW2MS000

section

attribute [-instance] _root_.OAI.MatroidProphet.withBotIntMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

namespace MainAlgorithm
variable {n : ℕ}

lemma listedTransferGap_parity_expectation_le (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ) (Y : Set (Fin n))
    (hY : Y ⊆ (trueGroup M d s i : Set (Fin n)))
    (hn : densityThreshold ≤ ((trueGroup M d s i).card : ℝ)) :
    tripleMaskExpectation (fun _ => (1:ℝ)/4) (fun _ => thinningRate) (fun _ => thinningRate)
      univ (fun A B C => fairParityExpectation (fun p =>
        listedTransferGap M hE (2^100) (withMasks d A B C) s i Y (boolParity p))) ≤
      2 * residualDelta * (trueGroup M d s i).card := by
  sorry

end MainAlgorithm
end MatroidProphet

end OAI
end
