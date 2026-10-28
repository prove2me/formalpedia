-- Prove2me | Theorems.Thm_OAI_SharpTerminalLeave_prefix_present_edge_closure
-- name    : OAI.SharpTerminalLeave.prefix_present_edge_closure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:55:25.424755+00:00
-- url     : https://prove2.me/theorems/27f2c58c-2b9e-4907-9415-b6030bc20546
-- title:
--   OAI.SharpTerminalLeave.prefix_present_edge_closure: intermediate lemma from OpenAI, The sharp terminal leave in random triangle removal
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpTerminalLeave.sharp_terminal_leave`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp terminal leave in random triangle removal*, OpenAI Math Release, September 25, 2026, result family 188, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpTerminalLeave.prefix_present_edge_closure` of [lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Process/CenteredEdgeVectorTriangle.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Process/CenteredEdgeVectorTriangle.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpTerminalLeave`, with `open scoped BigOperators`, `open Filter Classical`):
--
--   ```lean
--   theorem prefix_present_edge_closure : ∀ᶠ n : ℕ in atTop,
--       ∀ ω : History (Graph n) (prefixTime n),
--       ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
--       PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
--       PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω →
--       ∀ j ≤ prefixTime n, densityEdgeSafe n (earlyDensity n j) (prefixEdgeRadius n)
--         (ω (historyIndex (prefixTime n) j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpTerminalLeave.History`, `OAI.SharpTerminalLeave.PrefixBalancedNoise`, `OAI.SharpTerminalLeave.PrefixCodegreeNoiseGood`, `OAI.SharpTerminalLeave.PrefixRootedUpper`, `OAI.SharpTerminalLeave.PrefixTriangleNoise`, `OAI.SharpTerminalLeave.densityEdgeSafe`, `OAI.SharpTerminalLeave.earlyDensity`, `OAI.SharpTerminalLeave.historyIndex`, `OAI.SharpTerminalLeave.historyLaw`, `OAI.SharpTerminalLeave.prefixEdgeRadius` and `OAI.SharpTerminalLeave.prefixTime` (definitions bundle `OAIQ4Tr000` of this split); `OAI.SharpTerminalLeave.Graph`, `OAI.SharpTerminalLeave.completeGraph` and `OAI.SharpTerminalLeave.step` (the published bundle `Def_TriangleRemoval`).
--
--   **Used by.** The proofs of `OAI.SharpTerminalLeave.prefix_all_pair_closure` and `OAI.SharpTerminalLeave.prefix_good_history` of this split import it.
-- source:
--   OpenAI, The sharp terminal leave in random triangle removal, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 188; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Process/CenteredEdgeVectorTriangle.lean (declaration OAI.SharpTerminalLeave.prefix_present_edge_closure)

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

theorem prefix_present_edge_closure : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω →
    ∀ j ≤ prefixTime n, densityEdgeSafe n (earlyDensity n j) (prefixEdgeRadius n)
      (ω (historyIndex (prefixTime n) j)) := by
  sorry

end SharpTerminalLeave
end
end

end OAI
end
