-- Prove2me | Theorems.Thm_OAI_SharpTerminalLeave_goodPrefix_cavity_semigroup
-- name    : OAI.SharpTerminalLeave.goodPrefix_cavity_semigroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:53:54.801487+00:00
-- url     : https://prove2.me/theorems/0fad75fc-7450-4524-8aa8-05ed42860600
-- title:
--   OAI.SharpTerminalLeave.goodPrefix_cavity_semigroup: intermediate lemma from OpenAI, The sharp terminal leave in random triangle removal
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpTerminalLeave.sharp_terminal_leave`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp terminal leave in random triangle removal*, OpenAI Math Release, September 25, 2026, result family 188, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpTerminalLeave.goodPrefix_cavity_semigroup` of [lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Process/ActivePairMembership.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Process/ActivePairMembership.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpTerminalLeave`, with `open scoped BigOperators Topology Matrix.Norms.Operator`, `open MeasureTheory`, `open Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem goodPrefix_cavity_semigroup {c : ℝ} (hc : 0 < c) :
--       ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ J : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
--         ∀ (C : ℝ) (G : Graph n) (_h : GoodPrefixGraph n c C G),
--         ∀ s ∈ Set.Icc (0 : ℝ) (Real.log n),
--           ‖NormedSpace.exp ((-s) • cavityGenerator (activeHypergraph G) (prefixD n))‖ ≤
--             C₁*(1+Real.log n)^J
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpTerminalLeave.GoodPrefixGraph`, `OAI.SharpTerminalLeave.activeHypergraph`, `OAI.SharpTerminalLeave.cavityGenerator` and `OAI.SharpTerminalLeave.prefixD` (definitions bundle `OAIQ4Tr000` of this split); `OAI.SharpTerminalLeave.Graph` and `OAI.SharpTerminalLeave.triangles` (the published bundle `Def_TriangleRemoval`).
--
--   **Used by.** The proof of `OAI.SharpTerminalLeave.main_l2_prefix_failure_bound` of this split imports it.
-- source:
--   OpenAI, The sharp terminal leave in random triangle removal, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 188; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Process/ActivePairMembership.lean (declaration OAI.SharpTerminalLeave.goodPrefix_cavity_semigroup)

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000

section

attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem goodPrefix_cavity_semigroup {c : ℝ} (hc : 0 < c) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ J : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (C : ℝ) (G : Graph n) (_h : GoodPrefixGraph n c C G),
      ∀ s ∈ Set.Icc (0 : ℝ) (Real.log n),
        ‖NormedSpace.exp ((-s) • cavityGenerator (activeHypergraph G) (prefixD n))‖ ≤
          C₁*(1+Real.log n)^J := by
  sorry
end SharpTerminalLeave

end

end OAI
end
