-- Prove2me | Theorems.Thm_OAI_SharpTerminalLeave_averaged_singleton_grid_collision
-- name    : OAI.SharpTerminalLeave.averaged_singleton_grid_collision
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:53:30.601684+00:00
-- url     : https://prove2.me/theorems/27787984-b842-4bf8-af76-9b35f860a0c0
-- title:
--   OAI.SharpTerminalLeave.averaged_singleton_grid_collision: intermediate lemma from OpenAI, The sharp terminal leave in random triangle removal
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpTerminalLeave.sharp_terminal_leave`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp terminal leave in random triangle removal*, OpenAI Math Release, September 25, 2026, result family 188, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpTerminalLeave.averaged_singleton_grid_collision` of [lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Queries/CanonicalCollisionSingletonSum.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Queries/CanonicalCollisionSingletonSum.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpTerminalLeave`, with `open scoped BigOperators Topology Matrix.Norms.Operator`, `open MeasureTheory`, `open Filter MeasureTheory`, `open scoped BigOperators ENNReal Classical`, `open scoped BigOperators`, `open Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem averaged_singleton_grid_collision (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
--       ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
--       ∀ (hne : G.Nonempty) (N : ℕ) [NeZero N]
--       (b : ℕ → ℝ) (_hb : ∀ t, 0 ≤ b t) (_hq : GridRowQuality (triangleHypergraph G) N b)
--       (C : ℝ) (_hC : 1 ≤ C) (_hlower : ∀ t ≤ N, 1 ≤ C*b t)
--       (d k : ℕ) (_hkd : k ≤ d) (_hkN : k ≤ N),
--       pmfMean (PMF.uniformOfFinset G hne) (fun e =>
--           tracedCollisionProbability (triangleHypergraph G) N d k {e} none) ≤
--         (8192*C^3/prefixD n^50)*
--           Real.exp (45*prefixD n*prefixWeight (fun t => (2/(N : ℝ))*b t) k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpTerminalLeave.GoodPrefixGraph`, `OAI.SharpTerminalLeave.GridRowQuality`, `OAI.SharpTerminalLeave.pmfMean`, `OAI.SharpTerminalLeave.prefixD`, `OAI.SharpTerminalLeave.prefixWeight`, `OAI.SharpTerminalLeave.tracedCollisionProbability` and `OAI.SharpTerminalLeave.triangleHypergraph` (definitions bundle `OAIQ4Tr000` of this split); `OAI.SharpTerminalLeave.Graph` (the published bundle `Def_TriangleRemoval`).
--
--   **Used by.** The proof of `OAI.SharpTerminalLeave.main_l2_prefix_failure_bound` of this split imports it.
-- source:
--   OpenAI, The sharp terminal leave in random triangle removal, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 188; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Queries/CanonicalCollisionSingletonSum.lean (declaration OAI.SharpTerminalLeave.averaged_singleton_grid_collision)

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000

section

attribute [-instance] _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem averaged_singleton_grid_collision (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (hne : G.Nonempty) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (_hb : ∀ t, 0 ≤ b t) (_hq : GridRowQuality (triangleHypergraph G) N b)
    (C : ℝ) (_hC : 1 ≤ C) (_hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (_hkd : k ≤ d) (_hkN : k ≤ N),
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        tracedCollisionProbability (triangleHypergraph G) N d k {e} none) ≤
      (8192*C^3/prefixD n^50)*
        Real.exp (45*prefixD n*prefixWeight (fun t => (2/(N : ℝ))*b t) k) := by
  sorry

end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

end

end OAI
end
