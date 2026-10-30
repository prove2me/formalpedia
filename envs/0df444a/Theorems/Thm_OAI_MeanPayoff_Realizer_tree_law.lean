-- Prove2me | Theorems.Thm_OAI_MeanPayoff_Realizer_tree_law
-- name    : OAI.MeanPayoff.Realizer.tree_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:11:34.731226+00:00
-- url     : https://prove2.me/theorems/7edf6c31-cc02-4aa3-a7b9-e85ced6534bd
-- title:
--   OAI.MeanPayoff.Realizer.tree_law: intermediate lemma from OpenAI, Randomized quasipolynomial-time mean-payoff games
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.randomized_quasipolynomial_mean_payoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Randomized quasipolynomial-time mean-payoff games*, OpenAI Math Release, September 25, 2026, result family 104, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MeanPayoff.Realizer.tree_law` of [lean/OAI/Computability/RandomMean/Complexity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RandomMean/Complexity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MeanPayoff.Realizer`, with `open RegisterBits BinaryData TreeDevice TreeDevice.Certified RandomTree`):
--
--   ```lean
--    theorem tree_law (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e)
--       (G : Game) (f : List Bool→ℚ) :
--       (tree program (limit K e ⟨input G⟩) (RegisterBits.initial program (input G))).expect (fun c => f c.output)=
--         (gameSolve G).expect (fun out => f (List.ofFn out))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MeanPayoff.RandomTree.expect`, `OAI.MeanPayoff.RegisterBits.Config`, `OAI.MeanPayoff.TreeDevice.treeSize`, `OAI.MeanPayoff.TreeDevice.Certified.Count`, `OAI.MeanPayoff.TreeDevice.Certified.Digits`, `OAI.MeanPayoff.TreeDevice.Certified.W`, `OAI.MeanPayoff.TreeDevice.Certified.instEncodingBool`, `OAI.MeanPayoff.TreeDevice.Certified.instEncodingDigits`, `OAI.MeanPayoff.TreeDevice.Certified.instEncodingList`, `OAI.MeanPayoff.TreeDevice.Certified.instEncodingProd`, `OAI.MeanPayoff.TreeDevice.Certified.instEncodingUnit`, `OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord`, `OAI.MeanPayoff.TreeDevice.Graph.Count`, `OAI.MeanPayoff.TreeDevice.Graph.Edge`, `OAI.MeanPayoff.TreeDevice.Graph.Edges`, `OAI.MeanPayoff.TreeDevice.Graph.Vertex`, `OAI.MeanPayoff.TreeDevice.Graph.W`, `OAI.MeanPayoff.TreeDevice.Certified.Encoding`, `OAI.MeanPayoff.TreeDevice.Certified.RawBasic.Arena`, `OAI.MeanPayoff.TreeDevice.Certified.RawControl.Acc`, `OAI.MeanPayoff.TreeDevice.Certified.RawControl.Cell`, `OAI.MeanPayoff.TreeDevice.Certified.RawControl.Env`, `OAI.MeanPayoff.TreeDevice.Certified.RawControl.Pack`, `OAI.MeanPayoff.TreeDevice.Certified.RawControl.State` and `OAI.MeanPayoff.TreeDevice.Certified.RawControl.instEncodingPack` (definitions bundle `OAIQ117R000` of this split); `OAI.MeanPayoff.gameSolve`, `OAI.MeanPayoff.Realizer.limit`, `OAI.MeanPayoff.Realizer.postCost`, `OAI.MeanPayoff.Realizer.program`, `OAI.MeanPayoff.RegisterBits.initial`, `OAI.MeanPayoff.RegisterBits.tree`, `OAI.MeanPayoff.TreeDevice.Certified.PostCode.Input` and `OAI.MeanPayoff.TreeDevice.Certified.Preparation.Aux` (definitions bundle `OAIQ117R002` of this split); `OAI.MeanPayoff.Game` and `OAI.MeanPayoff.input` (the published bundle `Def_RandomizedMeanPayoff`).
--
--   **Used by.** The proof of `OAI.randomized_quasipolynomial_mean_payoff` of this split imports it.
-- source:
--   OpenAI, Randomized quasipolynomial-time mean-payoff games, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 104; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Randomized-quasipolynomial-time-mean-payoff-games-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RandomMean/Complexity.lean (declaration OAI.MeanPayoff.Realizer.tree_law)

import Mathlib
import Definitions.Def_RandomizedMeanPayoff
import Definitions.Def_OAIQ117R002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified RandomTree
 theorem tree_law (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e)
    (G : Game) (f : List Bool→ℚ) :
    (tree program (limit K e ⟨input G⟩) (RegisterBits.initial program (input G))).expect (fun c => f c.output)=
      (gameSolve G).expect (fun out => f (List.ofFn out)) := by
  sorry

end MeanPayoff.Realizer

end

end OAI
end
