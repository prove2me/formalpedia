-- Prove2me | Theorems.Thm_OAI_WitnessedSeparation_Grid_QuotedGrid_selection_candidates
-- name    : OAI.WitnessedSeparation.Grid.QuotedGrid.selection_candidates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T00:28:03.098159+00:00
-- url     : https://prove2.me/theorems/309f0b71-4fd7-4c5d-be23-4363d7a369b0
-- title:
--   OAI.WitnessedSeparation.Grid.QuotedGrid.selection_candidates: intermediate lemma from OpenAI, Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WitnessedChoice.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting*, OpenAI Math Release, September 24, 2026, result family 243, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WitnessedSeparation.Grid.QuotedGrid.selection_candidates` of [lean/OAI/Computability/WitnessedChoice/TreeCorrection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/WitnessedChoice/TreeCorrection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WitnessedSeparation.Grid.QuotedGrid`, with `open Classical WitnessedChoice WitnessedChoice.BGS Hereditary`, `open QuotedTerm QuotedFormula SourceSyntax SourceProgram`):
--
--   ```lean
--   lemma selection_candidates (p : Polynomial ℝ) (hp : GridResources p b)
--       (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
--       (x : Finset (Σ e : Edge n, LocalGroup e)) (hn : 1 ≤ n) :
--       (SourceProgram.program.body.selection (atomInput b) p
--         (tupleCode (List.ofFn (vertexCode b ∘ α)))).candidates (edgeState x) =
--         edgeState (gridCandidates α (anchoredParents α).treeEdges x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WitnessedChoice.tupleCode`, `OAI.WitnessedChoice.AnchoredTree.Resolving`, `OAI.WitnessedChoice.Selection`, `OAI.WitnessedSeparation.Grid.Atom`, `OAI.WitnessedSeparation.Grid.Edge`, `OAI.WitnessedSeparation.Grid.GridResources`, `OAI.WitnessedSeparation.Grid.LocalGroup`, `OAI.WitnessedSeparation.Grid.Scalar`, `OAI.WitnessedSeparation.Grid.Vertex`, `OAI.WitnessedSeparation.Grid.anchoredParents`, `OAI.WitnessedSeparation.Grid.anchoredTree`, `OAI.WitnessedSeparation.Grid.atomInput`, `OAI.WitnessedSeparation.Grid.boxGraph`, `OAI.WitnessedSeparation.Grid.edgeState`, `OAI.WitnessedSeparation.Grid.gridCandidates`, `OAI.WitnessedSeparation.Grid.instFintypeAtom`, `OAI.WitnessedSeparation.Grid.vertexCode`, `OAI.WitnessedChoice.BGS.ClosedGuardedProgram`, `OAI.WitnessedChoice.BGS.GuardedProgram.selection`, `OAI.WitnessedChoice.BGS.SourceProgram.program` and `OAI.WitnessedSeparation.Grid.ParentEdges.treeEdges` (definitions bundle `OAIQ4Wc000` of this split); `OAI.WitnessedSeparation.Hereditary.HF` (the published bundle `Def_WitnessedChoice`).
--
--   **Used by.** The proofs of `OAI.WitnessedSeparation.Grid.QuotedGrid.formula_value`, `OAI.WitnessedSeparation.Grid.QuotedGrid.selection_transitive` and `OAI_WitnessedSeparation_Grid_QuotedGrid_terminal_output` of this split import it.
-- source:
--   OpenAI, Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 243; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Witnessed-symmetric-choice-is-strictly-stronger-than-choiceless-polynomial-time-with-counting-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/WitnessedChoice/TreeCorrection.lean (declaration OAI.WitnessedSeparation.Grid.QuotedGrid.selection_candidates)

import Mathlib
import Definitions.Def_WitnessedChoice
import Definitions.Def_OAIQ4Wc000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax SourceProgram

attribute [local irreducible] QuotedTerm.nextEdges QuotedTerm.tree SourceSyntax.candidates

lemma selection_candidates (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hn : 1 ≤ n) :
    (SourceProgram.program.body.selection (atomInput b) p
      (tupleCode (List.ofFn (vertexCode b ∘ α)))).candidates (edgeState x) =
      edgeState (gridCandidates α (anchoredParents α).treeEdges x) := by
  sorry

end QuotedGrid

end

end WitnessedSeparation.Grid

end OAI
end
