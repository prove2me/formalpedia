-- Prove2me | Theorems.Thm_OAI_Falconer_Regularization_scalar_weak_block_projection
-- name    : OAI.Falconer.Regularization.scalar_weak_block_projection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:43:54.991991+00:00
-- url     : https://prove2.me/theorems/e115a404-c88b-44bb-91af-3d8006e16e78
-- title:
--   OAI.Falconer.Regularization.scalar_weak_block_projection: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.Regularization.scalar_weak_block_projection` of [lean/OAI/MeasureTheory/Falconer/Incidence/ScalarWeakBlockProjection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Incidence/ScalarWeakBlockProjection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer.Regularization`, with `open scoped Pointwise`):
--
--   ```lean
--    theorem scalar_weak_block_projection {κ K : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hK : 0 < K) :
--       ∃ B copies : ℕ, ∃ η : ℝ, 0 < B ∧ 0 < copies ∧ 0 < η ∧
--         ∀ M : ℕ, 0 < M → ∀ K0 Kadd : ℝ, 0 < K0 → 0 < Kadd →
--         Real.log K0 ≤ κ^2*(B:ℝ)*(M:ℝ)*Real.log 2/160 →
--         Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log (2*Kadd) ≤
--           (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 →
--         ∀ L : Finset (CellPath 1), L ⊆ cubePaths 1 (B*M) → L.Nonempty →
--         Real.log (L.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 →
--         ((scalarCells ((1/2:ℝ)^(B*M))
--           (L.image scalarPathCenter+L.image scalarPathCenter)).card:ℝ) ≤
--           Kadd*(scalarCells ((1/2:ℝ)^(B*M)) (L.image scalarPathCenter)).card →
--         (∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
--           scalarBallMass (L.image scalarPathCenter) u t ≤
--             K0*t^κ*((L.image scalarPathCenter).card:ℝ)) →
--         ∀ A : Finset ℝ, A.Nonempty → (∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1) →
--         (∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
--           scalarBallMass A u t ≤ K*t^κ*(A.card:ℝ)) →
--         ∃ t ∈ A, Real.exp (η*(M:ℝ)*Real.log 2)*(L.card:ℝ) <
--           ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
--             (L.image scalarPathCenter).image (fun x => t*x))).card:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.cubePaths` and `OAI.Falconer.Regularization.CellPath` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.scalarBallMass` and `OAI.Falconer.scalarCells` (definitions bundle `OAIQ088F001` of this split); `OAI.Falconer.scalarPathCenter` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI_Falconer_Regularization_scalar_bounded_projection` and `OAI.Falconer.Regularization.scalar_dyadic_projection` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Incidence/ScalarWeakBlockProjection.lean (declaration OAI.Falconer.Regularization.scalar_weak_block_projection)

import Mathlib
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_weak_block_projection {κ K : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hK : 0 < K) :
    ∃ B copies : ℕ, ∃ η : ℝ, 0 < B ∧ 0 < copies ∧ 0 < η ∧
      ∀ M : ℕ, 0 < M → ∀ K0 Kadd : ℝ, 0 < K0 → 0 < Kadd →
      Real.log K0 ≤ κ^2*(B:ℝ)*(M:ℝ)*Real.log 2/160 →
      Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log (2*Kadd) ≤
        (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      ∀ L : Finset (CellPath 1), L ⊆ cubePaths 1 (B*M) → L.Nonempty →
      Real.log (L.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2 →
      ((scalarCells ((1/2:ℝ)^(B*M))
        (L.image scalarPathCenter+L.image scalarPathCenter)).card:ℝ) ≤
        Kadd*(scalarCells ((1/2:ℝ)^(B*M)) (L.image scalarPathCenter)).card →
      (∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
        scalarBallMass (L.image scalarPathCenter) u t ≤
          K0*t^κ*((L.image scalarPathCenter).card:ℝ)) →
      ∀ A : Finset ℝ, A.Nonempty → (∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1) →
      (∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
        scalarBallMass A u t ≤ K*t^κ*(A.card:ℝ)) →
      ∃ t ∈ A, Real.exp (η*(M:ℝ)*Real.log 2)*(L.card:ℝ) <
        ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
          (L.image scalarPathCenter).image (fun x => t*x))).card:ℝ) := by
  sorry

end Falconer.Regularization

end OAI
end
