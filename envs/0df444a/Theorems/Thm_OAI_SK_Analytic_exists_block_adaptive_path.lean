-- Prove2me | Theorems.Thm_OAI_SK_Analytic_exists_block_adaptive_path
-- name    : OAI.SK.Analytic.exists_block_adaptive_path
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:56:30.391133+00:00
-- url     : https://prove2.me/theorems/b9226feb-084a-485a-8449-b5477869e756
-- title:
--   OAI.SK.Analytic.exists_block_adaptive_path: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.exists_block_adaptive_path` of [lean/OAI/Probability/SKBarriers/SKBarriers/Hierarchy/BlockAdaptivePath.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Hierarchy/BlockAdaptivePath.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators`, `open MeasureTheory ProbabilityTheory Filter`):
--
--   ```lean
--   theorem exists_block_adaptive_path {D N k : ℕ} (hN : 0 < N) (hk : 0 < k)
--       (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
--       {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
--       (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
--       ∃ q : ℝ → (Fin (k+1) → ℝ),
--         q 0 = (fun j => ((j.val:ℝ)+1)*η) ∧
--         (∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt q
--           (blockAdaptiveOverlap I a β (Real.sqrt (1-u),fun j => Real.sqrt (cumulativeGapMap k (q u) j)))
--             (Set.Icc (0:ℝ) 1) u) ∧
--         (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, η ≤ cumulativeGapMap k (q u) j) ∧
--         (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, q u j ≤ ((j.val:ℝ)+1)*η+u) ∧
--         (∀ u ∈ Set.Icc (0:ℝ) 1,
--           let U := blockExponent I (fun i => Real.sqrt (1-u)*a i)
--             (fun b => β*Real.sqrt (cumulativeGapMap k (q u) b))
--           (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹ *
--             hierarchyOverlapError (blockDimension D N k) (blockMass D N k) U
--               (fun s i => spin (s i)) (blockLevel D N k j)) ≤
--             20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.ParameterSpace`, `OAI.SK.Analytic.parameterNormedGroup` and `OAI.SK.Analytic.parameterNormedSpace` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.blockDimension`, `OAI.SK.Analytic.blockLevel`, `OAI.SK.Analytic.blockMass` and `OAI.SK.Analytic.cumulativeGapMap` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.blockAdaptiveOverlap` and `OAI.SK.Analytic.blockExponent` (definitions bundle `OAIQ036S002` of this split); `OAI.SK.Analytic.hierarchyOverlapError` (definitions bundle `OAIQ036S004` of this split); `OAI.SK.Config` and `OAI.SK.spin` (the published bundle `Def_SKBarriers`).
--
--   **Used by.** The proofs of `OAI.SK.Analytic.quenchedPressure_quantitative_finiteInf` and `OAI.SK.Analytic.quenchedPressure_tendsto_finiteParisiInf` of this split import it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Hierarchy/BlockAdaptivePath.lean (declaration OAI.SK.Analytic.exists_block_adaptive_path)

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004

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
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem exists_block_adaptive_path {D N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ q : ℝ → (Fin (k+1) → ℝ),
      q 0 = (fun j => ((j.val:ℝ)+1)*η) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt q
        (blockAdaptiveOverlap I a β (Real.sqrt (1-u),fun j => Real.sqrt (cumulativeGapMap k (q u) j)))
          (Set.Icc (0:ℝ) 1) u) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, η ≤ cumulativeGapMap k (q u) j) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, q u j ≤ ((j.val:ℝ)+1)*η+u) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1,
        let U := blockExponent I (fun i => Real.sqrt (1-u)*a i)
          (fun b => β*Real.sqrt (cumulativeGapMap k (q u) b))
        (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹ *
          hierarchyOverlapError (blockDimension D N k) (blockMass D N k) U
            (fun s i => spin (s i)) (blockLevel D N k j)) ≤
          20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))) := by
  sorry
end SK.Analytic

end
end

end

end OAI
end
