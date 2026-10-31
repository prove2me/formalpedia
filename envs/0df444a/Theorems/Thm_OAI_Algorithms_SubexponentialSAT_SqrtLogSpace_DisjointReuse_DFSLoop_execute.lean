-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSLoop_execute
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop.execute
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:43:33.215299+00:00
-- url     : https://prove2.me/theorems/11563456-b0a6-41db-99ca-e7b16d993ef6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop.execute: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop.execute` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSLoop.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSLoop.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop`, with `open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit`):
--
--   ```lean
--   theorem execute (k M : ℕ) (threshold : List Bool) (leaf : Code) (budget bound : ℕ)
--       (I : Frontier n → Data → Prop) (hM : 2 ≤ M)
--       (hboundary : ∀ s d, I s d → Boundary threshold s d)
--       (hspace : ∀ s d, I s d → ∀ i, (d.stacks i).length ≤ bound)
--       (hbody : ∀ (node : Node n) rest total d, I ⟨node :: rest, total⟩ d →
--         ∃ next t, t ≤ budget ∧ ∃ e, BoundedEval (body k leaf) t d e bound ∧
--           Transition k M ⟨node :: rest, total⟩ next ∧ I next e)
--       (s : Frontier n) (d : Data) (hI : I s d) :
--       ∃ visits t total e, t ≤ visits * (budget + 1) + 1 ∧
--         BoundedEval (loop k leaf) t d e bound ∧
--         Transitions k M visits s ⟨[], total⟩ ∧ I ⟨[], total⟩ e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Frontier`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Node`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Transition` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Transitions` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.Boundary` (definitions bundle `OAIQ081S099` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.body` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.loop` (definitions bundle `OAIQ081S136` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.normalized_loop` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/DFSLoop.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop.execute)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

theorem execute (k M : ℕ) (threshold : List Bool) (leaf : Code) (budget bound : ℕ)
    (I : Frontier n → Data → Prop) (hM : 2 ≤ M)
    (hboundary : ∀ s d, I s d → Boundary threshold s d)
    (hspace : ∀ s d, I s d → ∀ i, (d.stacks i).length ≤ bound)
    (hbody : ∀ (node : Node n) rest total d, I ⟨node :: rest, total⟩ d →
      ∃ next t, t ≤ budget ∧ ∃ e, BoundedEval (body k leaf) t d e bound ∧
        Transition k M ⟨node :: rest, total⟩ next ∧ I next e)
    (s : Frontier n) (d : Data) (hI : I s d) :
    ∃ visits t total e, t ≤ visits * (budget + 1) + 1 ∧
      BoundedEval (loop k leaf) t d e bound ∧
      Transitions k M visits s ⟨[], total⟩ ∧ I ⟨[], total⟩ e := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop
end
