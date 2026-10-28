-- Prove2me | Theorems.Thm_OAI_TraceReconstruction_source_level_energy
-- name    : OAI.TraceReconstruction.source_level_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:52:43.009578+00:00
-- url     : https://prove2.me/theorems/40c1a711-832e-467f-8dfa-3a3387139917
-- title:
--   OAI.TraceReconstruction.source_level_energy: intermediate lemma from OpenAI, Quantitative lower bounds for trace reconstruction
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TraceReconstruction.quantitative_sample_lower_bound`, `OAI.TraceReconstruction.superpolynomial_one_trace` and `OAI.TraceReconstruction.superpolynomial_sample_complexity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quantitative lower bounds for trace reconstruction*, OpenAI Math Release, September 24, 2026, result family 122, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TraceReconstruction.source_level_energy` of [lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Propagation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Propagation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TraceReconstruction`, with `open scoped ENNReal`, `open Filter`, `open scoped Topology`, `open scoped Classical`):
--
--   ```lean
--   theorem source_level_energy (B D i ell h k : ℕ) (C N F ω K : ℝ)
--       (hB : 2 ≤ B) (hi : i<D) (hN : 1 ≤ N) (hC : 1 ≤ C) (hF : 1 ≤ F) (hω : 0<ω)
--       (H : SourceArithmeticBounds C N F (sourceEpsilon B D) (sourceCancellationOrder B D)
--         (sourceDimension B i) ell h)
--       (hk : (k:ℝ) ≤ sourceMomentEnvelope B D)
--       (hK : 200*(C^(2*sourceDimension B i)*F)/ω ≤ K)
--       (hfac : 8*sourceWeightEnvelope B D*((2^(sourceCancellationOrder B D):ℕ):ℝ)^2 ≤ N^(sourceEpsilon B D))
--       (hbad : 384*sourceBadRoleFactor (sourceDimension B i-1) (sourceDegreeCutoff B) ≤ N^(sourceEpsilon B D))
--       (hforce : 192*(sourceForcedRoleFactor (sourceDimension B i-1) (sourceDegreeCutoff B)*
--           (sourceWeightEnvelope B D)^(2^(sourceDimension B i))*
--           sourceSkeletonPrefactor (sourceCancellationOrder B D) (sourceDimension B i-1) K) ≤ N^(sourceEpsilon B D))
--       (htail : 1536 ≤ N^(sourceEpsilon B D))
--       (hsmooth : sourceSmoothingPrefactor (sourceCancellationOrder B D) K ≤ N^(sourceEpsilon B D)) :
--       let b := sourceDimension B i
--       let ε := sourceEpsilon B D
--       let s := sourceCancellationOrder B D
--       let T := sourceBlockWindows N b ε
--       let t := sourceArithmeticTrials C N b ε ell h
--       let L := N^(-scaleA b 0 ε*totalScoreExponent B i/2)
--       (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤
--           N^(-((totalScoreExponent B i+1)*sourceGapFloor B)/2)/8) ∧
--       (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤ 1/2) ∧
--       (64*sourceSharpEnergyBudget T t s (b-1) (sourceDegreeCutoff B) ω
--          (N^(-20*sourceWorkSize B D)) (N^(-20*sourceWorkSize B D)) ((6*(2*k:ℕ):ℝ)*L) ≤
--          N^(-totalScoreExponent B (i+1))) ∧
--       (∀j<b,hiddenSmoothingBound (t j) s ω ≤ N^(-20*sourceWorkSize B D))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TraceReconstruction.SourceArithmeticBounds`, `OAI.TraceReconstruction.hiddenSmoothingBound`, `OAI.TraceReconstruction.scaleA`, `OAI.TraceReconstruction.sourceArithmeticTrials`, `OAI.TraceReconstruction.sourceBadRoleFactor`, `OAI.TraceReconstruction.sourceBlockWindows`, `OAI.TraceReconstruction.sourceCancellationOrder`, `OAI.TraceReconstruction.sourceDegreeCutoff`, `OAI.TraceReconstruction.sourceDimension`, `OAI.TraceReconstruction.sourceEpsilon`, `OAI.TraceReconstruction.sourceForcedRoleFactor`, `OAI.TraceReconstruction.sourceMomentEnvelope`, `OAI.TraceReconstruction.sourceSkeletonPrefactor`, `OAI.TraceReconstruction.sourceSmoothingPrefactor`, `OAI.TraceReconstruction.sourceSparseCount`, `OAI.TraceReconstruction.sourceWeightEnvelope` and `OAI.TraceReconstruction.totalScoreExponent` (definitions bundle `OAIQ9Tr000` of this split); `OAI.TraceReconstruction.sourceGapFloor` (definitions bundle `OAIQ9Tr001` of this split); `OAI.TraceReconstruction.sourceSharpEnergyBudget` and `OAI.TraceReconstruction.sourceWorkSize` (definitions bundle `OAIQ9Tr002` of this split).
--
--   **Used by.** The proof of `OAI.TraceReconstruction.source_level_all_budgets` of this split imports it.
-- source:
--   OpenAI, Quantitative lower bounds for trace reconstruction, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 122; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/TraceReconstruction/TraceReconstruction/Propagation.lean (declaration OAI.TraceReconstruction.source_level_energy)

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

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_level_energy (B D i ell h k : ℕ) (C N F ω K : ℝ)
    (hB : 2 ≤ B) (hi : i<D) (hN : 1 ≤ N) (hC : 1 ≤ C) (hF : 1 ≤ F) (hω : 0<ω)
    (H : SourceArithmeticBounds C N F (sourceEpsilon B D) (sourceCancellationOrder B D)
      (sourceDimension B i) ell h)
    (hk : (k:ℝ) ≤ sourceMomentEnvelope B D)
    (hK : 200*(C^(2*sourceDimension B i)*F)/ω ≤ K)
    (hfac : 8*sourceWeightEnvelope B D*((2^(sourceCancellationOrder B D):ℕ):ℝ)^2 ≤ N^(sourceEpsilon B D))
    (hbad : 384*sourceBadRoleFactor (sourceDimension B i-1) (sourceDegreeCutoff B) ≤ N^(sourceEpsilon B D))
    (hforce : 192*(sourceForcedRoleFactor (sourceDimension B i-1) (sourceDegreeCutoff B)*
        (sourceWeightEnvelope B D)^(2^(sourceDimension B i))*
        sourceSkeletonPrefactor (sourceCancellationOrder B D) (sourceDimension B i-1) K) ≤ N^(sourceEpsilon B D))
    (htail : 1536 ≤ N^(sourceEpsilon B D))
    (hsmooth : sourceSmoothingPrefactor (sourceCancellationOrder B D) K ≤ N^(sourceEpsilon B D)) :
    let b := sourceDimension B i
    let ε := sourceEpsilon B D
    let s := sourceCancellationOrder B D
    let T := sourceBlockWindows N b ε
    let t := sourceArithmeticTrials C N b ε ell h
    let L := N^(-scaleA b 0 ε*totalScoreExponent B i/2)
    (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤
        N^(-((totalScoreExponent B i+1)*sourceGapFloor B)/2)/8) ∧
    (((6*(2*k:ℕ):ℝ)*L)^2*(sourceSparseCount T s (b-1):ℝ) ≤ 1/2) ∧
    (64*sourceSharpEnergyBudget T t s (b-1) (sourceDegreeCutoff B) ω
       (N^(-20*sourceWorkSize B D)) (N^(-20*sourceWorkSize B D)) ((6*(2*k:ℕ):ℝ)*L) ≤
       N^(-totalScoreExponent B (i+1))) ∧
    (∀j<b,hiddenSmoothingBound (t j) s ω ≤ N^(-20*sourceWorkSize B D)) := by
  sorry

end TraceReconstruction
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
