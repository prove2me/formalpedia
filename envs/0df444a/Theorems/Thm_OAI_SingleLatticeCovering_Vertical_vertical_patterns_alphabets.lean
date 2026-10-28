-- Prove2me | Theorems.Thm_OAI_SingleLatticeCovering_Vertical_vertical_patterns_alphabets
-- name    : OAI.SingleLatticeCovering.Vertical.vertical_patterns_alphabets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:47:23.445024+00:00
-- url     : https://prove2.me/theorems/793615b7-27a7-4f2d-a66d-ef7825b1c8a9
-- title:
--   OAI.SingleLatticeCovering.Vertical.vertical_patterns_alphabets: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SingleLatticeCovering.Vertical.vertical_patterns_alphabets` of [lean/OAI/Geometry/LatticeCovering/Patterns.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/Patterns.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SingleLatticeCovering.Vertical`, with `open scoped BigOperators`, `open Real`, `open scoped BigOperators`, `open MeasureTheory ProbabilityTheory Set`, `open scoped BigOperators`, `open MeasureTheory Set`, `open Module Submodule MeasureTheory`, `open scoped BigOperators`, `open Real Filter Topology`, `open scoped BigOperators`, `open Filter Topology Asymptotics`, `open scoped BigOperators`, `open Classical`, `open scoped BigOperators`, `open Classical`, `open scoped BigOperators`, `open Classical`, `open scoped BigOperators`, `open Module MeasureTheory`, `open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry Filter Topology`, `open scoped BigOperators`):
--
--   ```lean
--   theorem vertical_patterns_alphabets :
--       ∃ cutoff : ℕ, 2 ≤ cutoff ∧ ∃ C k κ : ℝ, 0 < C ∧ 0 < k ∧ 0 < κ ∧
--         ∀ b₁ ≥ cutoff, ∃ B : Block, ∃ c : Chain B,
--           c.first.b=b₁ ∧ c.CeilingSizes ∧
--           (c.dim+B.terminalDim : ℝ) ≤ C*((b₁ : ℝ)+1) ∧
--           c.radiusSq+(B.terminalDim : ℝ) ≤ C*((b₁ : ℝ)*Real.log ((b₁ : ℝ)+1)+1) ∧
--           (∀ j, Real.log ((c.alphabets j).card+1 : ℝ) ≤
--             Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+(b₁ : ℝ)^2) ∧
--           ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
--             P.Nonempty ∧ SuffixBinary P ∧
--             (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧
--               c.det*gamma (y-c.fullLinear l) ≤ Real.exp (-k*(b₁ : ℝ)^(70/100 : ℝ))) ∧
--             (∃ t : Fin B.terminalDim → ℝ, ∀ l ∈ P, ∀ j, l (Fin.natAdd c.dim j)=t j) ∧
--             κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SingleLatticeCovering.Folded.gamma` (definitions bundle `OAIQ16Cd000` of this split); `OAI.SingleLatticeCovering.Vertical.Block`, `OAI.SingleLatticeCovering.Vertical.Chain`, `OAI.SingleLatticeCovering.Vertical.SuffixBinary`, `OAI.SingleLatticeCovering.Vertical.Block.terminalDim`, `OAI.SingleLatticeCovering.Vertical.Chain.CeilingSizes`, `OAI.SingleLatticeCovering.Vertical.Chain.FullVec`, `OAI.SingleLatticeCovering.Vertical.Chain.alphabets`, `OAI.SingleLatticeCovering.Vertical.Chain.dim`, `OAI.SingleLatticeCovering.Vertical.Chain.first`, `OAI.SingleLatticeCovering.Vertical.Chain.fullDim` and `OAI.SingleLatticeCovering.Vertical.Chain.radiusSq` (definitions bundle `OAIQ16Cd001` of this split); `OAI.SingleLatticeCovering.Vertical.Chain.FullResidual`, `OAI.SingleLatticeCovering.Vertical.Chain.det`, `OAI.SingleLatticeCovering.Vertical.Chain.fullLinear` and `OAI.SingleLatticeCovering.Vertical.Chain.fullRaw` (definitions bundle `OAIQ16Cd002` of this split).
--
--   **Used by.** The proof of `OAI.SingleLatticeCovering.Assembly.eventual_single_lattice_covering` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/Patterns.lean (declaration OAI.SingleLatticeCovering.Vertical.vertical_patterns_alphabets)

import Mathlib
import Definitions.Def_OAIQ16Cd002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry Filter Topology
open scoped BigOperators

theorem vertical_patterns_alphabets :
    ∃ cutoff : ℕ, 2 ≤ cutoff ∧ ∃ C k κ : ℝ, 0 < C ∧ 0 < k ∧ 0 < κ ∧
      ∀ b₁ ≥ cutoff, ∃ B : Block, ∃ c : Chain B,
        c.first.b=b₁ ∧ c.CeilingSizes ∧
        (c.dim+B.terminalDim : ℝ) ≤ C*((b₁ : ℝ)+1) ∧
        c.radiusSq+(B.terminalDim : ℝ) ≤ C*((b₁ : ℝ)*Real.log ((b₁ : ℝ)+1)+1) ∧
        (∀ j, Real.log ((c.alphabets j).card+1 : ℝ) ≤
          Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+(b₁ : ℝ)^2) ∧
        ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
          P.Nonempty ∧ SuffixBinary P ∧
          (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧
            c.det*gamma (y-c.fullLinear l) ≤ Real.exp (-k*(b₁ : ℝ)^(70/100 : ℝ))) ∧
          (∃ t : Fin B.terminalDim → ℝ, ∀ l ∈ P, ∀ j, l (Fin.natAdd c.dim j)=t j) ∧
          κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l) := by
  sorry

end SingleLatticeCovering.Vertical

end
end
end
end
end
end
end
end
end
end
end
end
end

end

end OAI
end
