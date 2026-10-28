-- Prove2me | Theorems.Thm_OAI_SharpTerminalLeave_prefix_edge_residual_bounds
-- name    : OAI.SharpTerminalLeave.prefix_edge_residual_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:55:09.468888+00:00
-- url     : https://prove2.me/theorems/46ece683-a64b-46c2-92c2-c94c08e95178
-- title:
--   OAI.SharpTerminalLeave.prefix_edge_residual_bounds: intermediate lemma from OpenAI, The sharp terminal leave in random triangle removal
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpTerminalLeave.sharp_terminal_leave`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp terminal leave in random triangle removal*, OpenAI Math Release, September 25, 2026, result family 188, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpTerminalLeave.prefix_edge_residual_bounds` of [lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Tracking/PrefixEdgeResidualBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Tracking/PrefixEdgeResidualBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpTerminalLeave`, with `open scoped BigOperators`, `open Filter Classical Matrix`):
--
--   ```lean
--   theorem prefix_edge_residual_bounds : ∀ᶠ n : ℕ in atTop,
--       ∀ ω : History (Graph n) (prefixTime n),
--       ∀ hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support,
--       PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
--       ∀ j ≤ prefixTime n,
--       historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
--       ∀ i < j, ∀ z : CompleteEdge n → ℝ,
--       activeLinf (graphActive (ω (historyIndex (prefixTime n) i))) (prefixEdgeResidual ω hω i z) ≤
--         6*activeLinf (graphActive (ω (historyIndex (prefixTime n) i))) z ∧
--       activeL2 (graphActive (ω (historyIndex (prefixTime n) i))) (prefixEdgeResidual ω hω i z) ≤
--         (2*prefixSpectralError n (1/80000))*activeL2 (graphActive (ω (historyIndex (prefixTime n) i))) z
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpTerminalLeave.CompleteEdge`, `OAI.SharpTerminalLeave.History`, `OAI.SharpTerminalLeave.PrefixBalancedNoise`, `OAI.SharpTerminalLeave.PrefixRootedUpper`, `OAI.SharpTerminalLeave.activeL2`, `OAI.SharpTerminalLeave.activeLinf`, `OAI.SharpTerminalLeave.densityEdgeSafe`, `OAI.SharpTerminalLeave.earlyDensity`, `OAI.SharpTerminalLeave.graphActive`, `OAI.SharpTerminalLeave.historyAlive`, `OAI.SharpTerminalLeave.historyIndex`, `OAI.SharpTerminalLeave.historyLaw`, `OAI.SharpTerminalLeave.prefixEdgeRadius`, `OAI.SharpTerminalLeave.prefixEdgeResidual`, `OAI.SharpTerminalLeave.prefixSpectralError` and `OAI.SharpTerminalLeave.prefixTime` (definitions bundle `OAIQ4Tr000` of this split); `OAI.SharpTerminalLeave.Graph`, `OAI.SharpTerminalLeave.completeGraph` and `OAI.SharpTerminalLeave.step` (the published bundle `Def_TriangleRemoval`).
--
--   **Used by.** The proof of `OAI.SharpTerminalLeave.prefix_present_edge_closure` of this split imports it.
-- source:
--   OpenAI, The sharp terminal leave in random triangle removal, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 188; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Tracking/PrefixEdgeResidualBounds.lean (declaration OAI.SharpTerminalLeave.prefix_edge_residual_bounds)

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
open Filter Classical Matrix

namespace SharpTerminalLeave

theorem prefix_edge_residual_bounds : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ∀ hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support,
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    ∀ i < j, ∀ z : CompleteEdge n → ℝ,
    activeLinf (graphActive (ω (historyIndex (prefixTime n) i))) (prefixEdgeResidual ω hω i z) ≤
      6*activeLinf (graphActive (ω (historyIndex (prefixTime n) i))) z ∧
    activeL2 (graphActive (ω (historyIndex (prefixTime n) i))) (prefixEdgeResidual ω hω i z) ≤
      (2*prefixSpectralError n (1/80000))*activeL2 (graphActive (ω (historyIndex (prefixTime n) i))) z := by
  sorry

end SharpTerminalLeave
end
end

end OAI
end
