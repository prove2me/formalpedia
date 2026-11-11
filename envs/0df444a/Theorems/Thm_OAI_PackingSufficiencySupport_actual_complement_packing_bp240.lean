-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_actual_complement_packing_bp240
-- name    : OAI.PackingSufficiencySupport.actual_complement_packing_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:50:05.551881+00:00
-- url     : https://prove2.me/theorems/b96e663a-faa0-4438-975d-af42ec5c3e53
-- title:
--   OAI.PackingSufficiencySupport.actual_complement_packing_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.actual_complement_packing` of [lean/OAI/Geometry/BallPacking/Packings/ComplementPacking.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Packings/ComplementPacking.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport`, with `open scoped ContDiff Manifold Topology BigOperators`, `open Set Function Manifold`, `open Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit`):
--
--   ```lean
--    theorem actual_complement_packing_bp240 (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
--       (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
--       (hrr : ∀ i,r' i < r i) {a₀ : ℝ} (ha₀ : 0<a₀) (ha₁ : a₀<1)
--       (hrs : ∀ i,r i<1-a₀) (hhalf : ∀ i,r i<1/2)
--       (hvol : ∑ i,r i^(m+4)<1-a₀^(m+4)) :
--       ∃ b : ℝ,b<1-a₀ ∧ ∃ f : Fin N → Ambient (m+4) → Ambient (m+4),
--         (∀ i,IsBallEmbedding (r' i) (f i)) ∧
--         (∀ i,f i '' closedBall (m+4) (r' i)⊆openBall (m+4) 1) ∧
--         (∀ i,∀ x∈closedBall (m+4) (r' i),Real.pi*Complex.normSq (f i x 0)<b) ∧
--         Pairwise (fun i j => Disjoint (f i '' closedBall (m+4) (r' i))
--           (f j '' closedBall (m+4) (r' j)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Ambient` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.IsBallEmbedding`, `OAI.PackingSufficiencySupport.closedBall` and `OAI.PackingSufficiencySupport.openBall` (definitions bundle `OAIQ240Bp007` of this split).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.main_theorem` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Packings/ComplementPacking.lean (declaration OAI.PackingSufficiencySupport.actual_complement_packing)

import Mathlib
import Definitions.Def_OAIQ240Bp007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian DiagonalQuadrics DiagonalQuadrics.Explicit

 theorem actual_complement_packing_bp240 (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) {a₀ : ℝ} (ha₀ : 0<a₀) (ha₁ : a₀<1)
    (hrs : ∀ i,r i<1-a₀) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+4)<1-a₀^(m+4)) :
    ∃ b : ℝ,b<1-a₀ ∧ ∃ f : Fin N → Ambient (m+4) → Ambient (m+4),
      (∀ i,IsBallEmbedding (r' i) (f i)) ∧
      (∀ i,f i '' closedBall (m+4) (r' i)⊆openBall (m+4) 1) ∧
      (∀ i,∀ x∈closedBall (m+4) (r' i),Real.pi*Complex.normSq (f i x 0)<b) ∧
      Pairwise (fun i j => Disjoint (f i '' closedBall (m+4) (r' i))
        (f j '' closedBall (m+4) (r' j))) := by
  sorry

end PackingSufficiencySupport

end

end OAI
end
