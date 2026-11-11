-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_Signing_Stack_runsPoly_simultaneousSigns
-- name    : OAI.AlgorithmicThinTrees.Signing.Stack.runsPoly_simultaneousSigns
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:13:57.307708+00:00
-- url     : https://prove2.me/theorems/11eefb2b-d969-486c-8fd0-553bfe2fb0a9
-- title:
--   OAI.AlgorithmicThinTrees.Signing.Stack.runsPoly_simultaneousSigns: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.Signing.Stack.runsPoly_simultaneousSigns` of [lean/OAI/Combinatorics/ThinTrees/Signing/Realization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Signing/Realization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.Signing.Stack`, with `open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix`):
--
--   ```lean
--   lemma runsPoly_simultaneousSigns {ι : Type*} {L : ι → ℕ} (a : ι → FormPair)
--       (ha : IsPoly L (fun i => (formsCode (a i)).length))
--       (hA : ∀i,((a i).a.2.map (fun q : ℚ => (q:ℝ))).PosDef)
--       (hB : ∀i,((a i).b.2.map (fun q : ℚ => (q:ℝ))).PosDef) :
--       RunsPoly L simultaneousSigns a
--   ```
--
--   **Definitions.** The statement is written with `OAI.AlgorithmicThinTrees.FormSigning.whiten`, `OAI.AlgorithmicThinTrees.RationalGram.factorColumns`, `OAI.AlgorithmicThinTrees.RationalInverse.inverse`, `OAI.AlgorithmicThinTrees.RationalSigning.input`, `OAI.AlgorithmicThinTrees.StackedSigning.stack`, `OAI.CurrentKS.RationalInput.signing`, `OAI.CurrentKS.Realization.boolCode` and `OAI.CurrentKS.Realization.listCode` (definitions bundle `OAIQ241TT000` of this split); `OAI.AlgorithmicThinTrees.Signing.Stack.FormPair` (definitions bundle `OAIQ241TT001` of this split); `OAI.CurrentKS.Realization.IsPoly` and `OAI.CurrentKS.Realization.RunsPoly` (definitions bundle `OAIQ241TT006` of this split); `OAI.AlgorithmicThinTrees.Signing.Stack.formsCode` (definitions bundle `OAIQ241TT009` of this split); `OAI.AlgorithmicThinTrees.Signing.Stack.simultaneousSigns` (definitions bundle `OAIQ241TT014` of this split).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.sparsify_program_polynomial` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Signing/Realization.lean (declaration OAI.AlgorithmicThinTrees.Signing.Stack.runsPoly_simultaneousSigns)

import Mathlib
import Definitions.Def_OAIQ241TT014

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix

lemma runsPoly_simultaneousSigns {ι : Type*} {L : ι → ℕ} (a : ι → FormPair)
    (ha : IsPoly L (fun i => (formsCode (a i)).length))
    (hA : ∀i,((a i).a.2.map (fun q : ℚ => (q:ℝ))).PosDef)
    (hB : ∀i,((a i).b.2.map (fun q : ℚ => (q:ℝ))).PosDef) :
    RunsPoly L simultaneousSigns a := by
  sorry

end AlgorithmicThinTrees.Signing.Stack
end

end OAI
end
