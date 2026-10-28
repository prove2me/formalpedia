-- Prove2me | Theorems.Thm_OAI_BinaryCoordinateSweeps_sparse_finite_radius
-- name    : OAI.BinaryCoordinateSweeps.sparse_finite_radius
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T15:59:55.87381+00:00
-- url     : https://prove2.me/theorems/2d6c019b-6d6e-4063-8e9d-dbd4622987a9
-- title:
--   OAI.BinaryCoordinateSweeps.sparse_finite_radius: intermediate lemma from OpenAI, Row–column symmetry and contraction of coordinate sweeps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.binary_sweep_contraction_and_mixing`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Row–column symmetry and contraction of coordinate sweeps*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BinaryCoordinateSweeps.sparse_finite_radius` of [lean/OAI/Probability/BinarySweep/SparseBounds/FewSparse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BinarySweep/SparseBounds/FewSparse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BinaryCoordinateSweeps`, with `open scoped BigOperators Classical`, `open Filter Topology`):
--
--   ```lean
--   theorem sparse_finite_radius (r : ℕ) (hr : 2 ≤ r) :
--       ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℕ, 1 ≤ b → b ≤ 16000 →
--         ∀bits : Fin b → ℕ, (∀j, r ≤ bits j ∧ bits j ≤ 2*r) →
--         ∀h k : ℕ, h ≤ gridSize bits → k ≤ gridSize bits →
--         (10:ℝ)^26 ≤ Real.log (gridSize bits) → 1 ≤ k →
--         ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ) → h ≤ 100000*k →
--         ∀H : PathFamily bits h, ∀z : ℝ, 0 ≤ z → z ≤ δ → sparseEndpointBound H k z
--   ```
--
--   **Definitions.** The statement is written with `OAI.BinaryCoordinateSweeps.PathFamily`, `OAI.BinaryCoordinateSweeps.gridSize` and `OAI.BinaryCoordinateSweeps.sparseEndpointBound` (definitions bundle `OAIB3Bs000` of this split).
--
--   **Used by.** The proof of `OAI.BinaryCoordinateSweeps.sparse_uniform_radius` of this split imports it.
-- source:
--   OpenAI, Row–column symmetry and contraction of coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BinarySweep/SparseBounds/FewSparse.lean (declaration OAI.BinaryCoordinateSweeps.sparse_finite_radius)

import Mathlib
import Definitions.Def_OAIB3Bs000

section

attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical
open Filter Topology

namespace BinaryCoordinateSweeps

theorem sparse_finite_radius (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℕ, 1 ≤ b → b ≤ 16000 →
      ∀bits : Fin b → ℕ, (∀j, r ≤ bits j ∧ bits j ≤ 2*r) →
      ∀h k : ℕ, h ≤ gridSize bits → k ≤ gridSize bits →
      (10:ℝ)^26 ≤ Real.log (gridSize bits) → 1 ≤ k →
      ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ) → h ≤ 100000*k →
      ∀H : PathFamily bits h, ∀z : ℝ, 0 ≤ z → z ≤ δ → sparseEndpointBound H k z := by
  sorry

end BinaryCoordinateSweeps

end

end OAI
end
