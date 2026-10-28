-- Prove2me | Theorems.Thm_OAI_WitnessedSeparation_Grid_QuotedGrid_fundamentalPool_in_cycles
-- name    : OAI.WitnessedSeparation.Grid.QuotedGrid.fundamentalPool_in_cycles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T00:22:56.183175+00:00
-- url     : https://prove2.me/theorems/cdc4efed-6dad-4dc2-81f3-ff4fb340869d
-- title:
--   OAI.WitnessedSeparation.Grid.QuotedGrid.fundamentalPool_in_cycles: intermediate lemma from OpenAI, Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WitnessedChoice.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting*, OpenAI Math Release, September 24, 2026, result family 243, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WitnessedSeparation.Grid.QuotedGrid.fundamentalPool_in_cycles` of [lean/OAI/Computability/WitnessedChoice/TreeCorrection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/WitnessedChoice/TreeCorrection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WitnessedSeparation.Grid.QuotedGrid`, with `open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools`, `open QuotedTerm QuotedFormula SourceSyntax`):
--
--   ```lean
--   lemma fundamentalPool_in_cycles (env : Fin k → HF (Atom b)) (V E F R T H N : QuotedTerm k)
--       (P : ParentEdges T₀) (Ns : Finset (Edge n))
--       (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
--       (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
--       (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
--       (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
--       (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
--       (hH : H.meaning (atomInput b) env = connTableCode b P.treeEdges)
--       (hN : N.meaning (atomInput b) env = ofFinset (Ns.image (edgeCode b)))
--       (hoff : ∀ e ∈ Ns, e ∉ P.treeEdges) (hn : 1 ≤ n) :
--       ∀ r ∈ P.fundamentalPool Ns,
--         relationCode r ∈ elements ((cycleRelations V E F R T H N).meaning (atomInput b) env)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WitnessedChoice.BGS.QuotedTerm`, `OAI.WitnessedChoice.BGS.relationCode`, `OAI.WitnessedChoice.RelationPools.Relation`, `OAI.WitnessedChoice.TreeTest.RootedTree`, `OAI.WitnessedSeparation.Grid.Atom`, `OAI.WitnessedSeparation.Grid.CycleFrame`, `OAI.WitnessedSeparation.Grid.Edge`, `OAI.WitnessedSeparation.Grid.EdgeX`, `OAI.WitnessedSeparation.Grid.EdgeY`, `OAI.WitnessedSeparation.Grid.EdgeZ`, `OAI.WitnessedSeparation.Grid.ParentEdges`, `OAI.WitnessedSeparation.Grid.Scalar`, `OAI.WitnessedSeparation.Grid.Vertex`, `OAI.WitnessedSeparation.Grid.atomInput`, `OAI.WitnessedSeparation.Grid.boxGraph`, `OAI.WitnessedSeparation.Grid.connTableCode`, `OAI.WitnessedSeparation.Grid.distancesCode`, `OAI.WitnessedSeparation.Grid.edgeCode`, `OAI.WitnessedSeparation.Grid.frameCode`, `OAI.WitnessedSeparation.Grid.instFintypeAtom`, `OAI.WitnessedSeparation.Grid.vertexCode`, `OAI.WitnessedChoice.BGS.SourceSyntax.cycleRelations`, `OAI.WitnessedSeparation.Grid.ParentEdges.fundamentalPool` and `OAI.WitnessedSeparation.Grid.ParentEdges.treeEdges` (definitions bundle `OAIQ4Wc000` of this split); `OAI.WitnessedSeparation.Hereditary.HF`, `OAI.WitnessedSeparation.Hereditary.elements` and `OAI.WitnessedSeparation.Hereditary.ofFinset` (the published bundle `Def_WitnessedChoice`).
--
--   **Used by.** The proof of `OAI.WitnessedSeparation.Grid.QuotedGrid.selection_transitive` of this split imports it.
-- source:
--   OpenAI, Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 243; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Witnessed-symmetric-choice-is-strictly-stronger-than-choiceless-polynomial-time-with-counting-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/WitnessedChoice/TreeCorrection.lean (declaration OAI.WitnessedSeparation.Grid.QuotedGrid.fundamentalPool_in_cycles)

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

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ} {T₀ : RootedTree (Vertex n)}

attribute [local irreducible] SourceSyntax.cycleRelations SourceSyntax.cycleY

lemma fundamentalPool_in_cycles (env : Fin k → HF (Atom b)) (V E F R T H N : QuotedTerm k)
    (P : ParentEdges T₀) (Ns : Finset (Edge n))
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hH : H.meaning (atomInput b) env = connTableCode b P.treeEdges)
    (hN : N.meaning (atomInput b) env = ofFinset (Ns.image (edgeCode b)))
    (hoff : ∀ e ∈ Ns, e ∉ P.treeEdges) (hn : 1 ≤ n) :
    ∀ r ∈ P.fundamentalPool Ns,
      relationCode r ∈ elements ((cycleRelations V E F R T H N).meaning (atomInput b) env) := by
  sorry

end QuotedGrid

end

end WitnessedSeparation.Grid

end OAI
end
