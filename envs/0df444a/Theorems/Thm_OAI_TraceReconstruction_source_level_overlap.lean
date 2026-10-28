-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_source_level_overlap
-- name    : OAI.TraceReconstruction.source_level_overlap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:54:24.801071+00:00
-- url     : https://prove2.me/theorems/683ee320-3a09-4876-ae1d-2c4590db3f5e
-- title:
--   OAI.TraceReconstruction.source_level_overlap: intermediate lemma from OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TraceReconstruction.source_level_overlap` of [lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Induction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Induction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TraceReconstruction`, with `open scoped ENNReal`, `open Filter`, `open scoped Topology`, `open scoped Classical`):
--
--   ```lean
--   theorem source_level_overlap {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
--       (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
--       (hq' : q∈Set.Ioc 0 (1/2:ℝ))
--       (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
--       (htail : 2*(B:ℝ)*Real.exp
--         (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
--           n^(-sourceTailExponent B D)) :
--       let N := sourceTargetScale B D n (i+1)
--       let b := sourceDimension B i
--       let ε := sourceEpsilon B D
--       let s := sourceCancellationOrder B D
--       let P := sourceArithmeticP (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
--       let h := sourceArithmeticCount (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
--       let atom := fun (τ : Bool)=>if τ then U.right else U.left
--       ∀j ≤ b, initialOverlapLower q ≤ listTraceOverlap q hq
--         (pureAtomRun (sourceBlockWord s P atom j false) (h j))
--         (pureAtomRun (sourceBlockWord s P atom j false) (h j+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TraceReconstruction.SourceLevelPair`, `OAI.TraceReconstruction.SourceNumericMargins`, `OAI.TraceReconstruction.initialOverlapLower`, `OAI.TraceReconstruction.listTraceOverlap`, `OAI.TraceReconstruction.pureAtomRun`, `OAI.TraceReconstruction.sourceArithmeticCount`, `OAI.TraceReconstruction.sourceArithmeticP`, `OAI.TraceReconstruction.sourceBlockWord`, `OAI.TraceReconstruction.sourceCancellationOrder`, `OAI.TraceReconstruction.sourceDimension`, `OAI.TraceReconstruction.sourceEpsilon`, `OAI.TraceReconstruction.sourceHalfMoment`, `OAI.TraceReconstruction.sourceOverlapConstant`, `OAI.TraceReconstruction.sourceTargetScale`, `OAI.TraceReconstruction.totalScoreExponent` and `OAI.TraceReconstruction.ConcreteLevelPair` (definitions bundle `OAIQ9Tr000` of this split); `OAI.TraceReconstruction.sourceTailDenominator` and `OAI.TraceReconstruction.sourceTailExponent` (definitions bundle `OAIQ9Tr002` of this split).
--
--   **Used by.** The proofs of `OAI.TraceReconstruction.source_all_levels_eventually` and `OAI_TraceReconstruction_source_level_step` of this split import it.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Induction.lean (declaration OAI.TraceReconstruction.source_level_overlap)

import Mathlib
import Definitions.Def_OAIQ9Tr002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_level_overlap {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ))
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    let N := sourceTargetScale B D n (i+1)
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let P := sourceArithmeticP (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    let h := sourceArithmeticCount (sourceOverlapConstant q) N b ε U.left.length U.overlapCount
    let atom := fun (τ : Bool)=>if τ then U.right else U.left
    ∀j ≤ b, initialOverlapLower q ≤ listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)) := by
  sorry

end TraceReconstruction

end
end
end
end
end
end
end

end OAI
end
