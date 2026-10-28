-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_source_level_warmup_second
-- name    : OAI.TraceReconstruction.source_level_warmup_second
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:53:09.822497+00:00
-- url     : https://prove2.me/theorems/076ae0f2-e7a8-43b1-af25-3fc59f05a37d
-- title:
--   OAI.TraceReconstruction.source_level_warmup_second: intermediate lemma from OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TraceReconstruction.source_level_warmup_second` of [lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Induction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Induction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TraceReconstruction`, with `open scoped ENNReal`, `open Filter`, `open scoped Topology`, `open scoped Classical`):
--
--   ```lean
--   theorem source_level_warmup_second {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
--       (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
--       (hq' : q∈Set.Ioc 0 (1/2:ℝ)) (hiw : i<warmupBlocks B)
--       (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
--       (htail : 2*(B:ℝ)*Real.exp
--         (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
--           n^(-sourceTailExponent B D)) :
--       let N := sourceTargetScale B D n (i+1)
--       let ε := sourceEpsilon B D
--       let s := sourceCancellationOrder B D
--       let T := sourceBlockWindows N 2 ε
--       let t := sourceArithmeticTrials (sourceOverlapConstant q) N 2 ε U.left.length U.overlapCount
--       let P := sourceArithmeticP (sourceOverlapConstant q) N 2 ε U.left.length U.overlapCount
--       let h := sourceArithmeticCount (sourceOverlapConstant q) N 2 ε U.left.length U.overlapCount
--       let k := sourceHalfMoment B D n (i+1)
--       let L := N^(-scaleA 2 0 ε*totalScoreExponent B i/2)
--       let a := N^(-20*sourceWorkSize B D)
--       let ω := initialOverlapLower q
--       let cost := sourceClippingCost (fun _=>T 0) (fun _=>t 0) s 0 k ω a L
--       (((6*(2*k:ℕ):ℝ)*L)^2*(2:ℝ)^s ≤ 1/2) ∧ cost ≤ 1/2 ∧
--       Real.sqrt (((h 2+1:ℕ):ℝ)*((2^s:ℕ):ℝ)*
--         (64*sourceSharpEnergyBudget (fun _=>T 0) (fun _=>t 0) s 0 2 ω a a ((6*(2*k:ℕ):ℝ)*L)))+
--         2*((h 2+1:ℕ):ℝ)*((P 1:ℝ)*(cost+(T 0:ℝ)*U.error)) ≤ 1/4
--   ```
--
--   **Definitions.** The statement is written with `OAI.TraceReconstruction.SourceLevelPair`, `OAI.TraceReconstruction.SourceNumericMargins`, `OAI.TraceReconstruction.initialOverlapLower`, `OAI.TraceReconstruction.scaleA`, `OAI.TraceReconstruction.sourceArithmeticCount`, `OAI.TraceReconstruction.sourceArithmeticP`, `OAI.TraceReconstruction.sourceArithmeticTrials`, `OAI.TraceReconstruction.sourceBlockWindows`, `OAI.TraceReconstruction.sourceCancellationOrder`, `OAI.TraceReconstruction.sourceEpsilon`, `OAI.TraceReconstruction.sourceHalfMoment`, `OAI.TraceReconstruction.sourceOverlapConstant`, `OAI.TraceReconstruction.sourceTargetScale`, `OAI.TraceReconstruction.totalScoreExponent`, `OAI.TraceReconstruction.warmupBlocks` and `OAI.TraceReconstruction.ConcreteLevelPair` (definitions bundle `OAIQ9Tr000` of this split); `OAI.TraceReconstruction.sourceClippingCost`, `OAI.TraceReconstruction.sourceSharpEnergyBudget`, `OAI.TraceReconstruction.sourceTailDenominator`, `OAI.TraceReconstruction.sourceTailExponent` and `OAI.TraceReconstruction.sourceWorkSize` (definitions bundle `OAIQ9Tr002` of this split).
--
--   **Used by.** The proof of `OAI.TraceReconstruction.source_level_overlap` of this split imports it.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Induction.lean (declaration OAI.TraceReconstruction.source_level_warmup_second)

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
namespace TraceReconstruction
open scoped Classical

theorem source_level_warmup_second {B D i : ℕ} {n q : ℝ} {hq : q∈Set.Icc 0 1}
    (U : SourceLevelPair B D n q hq i) (hB : 2 ≤ B) (hi : i<D) (hn : 4 ≤ n)
    (hq' : q∈Set.Ioc 0 (1/2:ℝ)) (hiw : i<warmupBlocks B)
    (H : SourceNumericMargins B D q (sourceTargetScale B D n (i+1)))
    (htail : 2*(B:ℝ)*Real.exp
      (-(sourceTargetScale B D n (i+1))^(sourceEpsilon B D)/sourceTailDenominator B D q) ≤
        n^(-sourceTailExponent B D)) :
    let N := sourceTargetScale B D n (i+1)
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let T := sourceBlockWindows N 2 ε
    let t := sourceArithmeticTrials (sourceOverlapConstant q) N 2 ε U.left.length U.overlapCount
    let P := sourceArithmeticP (sourceOverlapConstant q) N 2 ε U.left.length U.overlapCount
    let h := sourceArithmeticCount (sourceOverlapConstant q) N 2 ε U.left.length U.overlapCount
    let k := sourceHalfMoment B D n (i+1)
    let L := N^(-scaleA 2 0 ε*totalScoreExponent B i/2)
    let a := N^(-20*sourceWorkSize B D)
    let ω := initialOverlapLower q
    let cost := sourceClippingCost (fun _=>T 0) (fun _=>t 0) s 0 k ω a L
    (((6*(2*k:ℕ):ℝ)*L)^2*(2:ℝ)^s ≤ 1/2) ∧ cost ≤ 1/2 ∧
    Real.sqrt (((h 2+1:ℕ):ℝ)*((2^s:ℕ):ℝ)*
      (64*sourceSharpEnergyBudget (fun _=>T 0) (fun _=>t 0) s 0 2 ω a a ((6*(2*k:ℕ):ℝ)*L)))+
      2*((h 2+1:ℕ):ℝ)*((P 1:ℝ)*(cost+(T 0:ℝ)*U.error)) ≤ 1/4 := by
  sorry

end TraceReconstruction

end
end
end
end
end
end

end OAI
end
