-- Prove2me | Theorems.Thm_OAI_BinaryCoordinateSweeps_sparse_uniform_radius
-- name    : OAI.BinaryCoordinateSweeps.sparse_uniform_radius
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T15:58:32.325368+00:00
-- url     : https://prove2.me/theorems/ab035c9f-164f-44ab-8084-2d6a6a5406c7
-- title:
--   OAI.BinaryCoordinateSweeps.sparse_uniform_radius: intermediate lemma from OpenAI, Row–column symmetry and contraction of coordinate sweeps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.binary_sweep_contraction_and_mixing`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Row–column symmetry and contraction of coordinate sweeps*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BinaryCoordinateSweeps.sparse_uniform_radius` of [lean/OAI/Probability/BinarySweep/SparseBounds/ManySparse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BinarySweep/SparseBounds/ManySparse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BinaryCoordinateSweeps`, with `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open Filter`, `open Sparse Young Irrep`):
--
--   ```lean
--   theorem sparse_uniform_radius : ∃ S : ℕ, ∀ r : ℕ, 2 ≤ r →
--       4000000000 ≤ (r:ℝ)*Real.log 2 →
--       ∃ δ : ℝ, 0<δ ∧ δ≤linePerturbationRadius r ∧ ∀ s : ℕ, S ≤ s →
--       ∀ b h k : ℕ, ∀bits : Fin b → ℕ, gridSize bits=s → 1≤b →
--       (∀j,r≤bits j ∧ bits j≤2*r) → (10:ℝ)^26≤Real.log s → 1≤k →
--       ((k+h:ℕ):ℝ)≤(s:ℝ)^(1599/1600:ℝ) → h≤100000*k →
--       ∀H : PathFamily bits h, ∀μ : YoungDiagram, ∀e : Cell μ ≃ FreeSlot H 0,
--       ∀_a : Tail μ ≃ Fin k, ∀z : ℝ, 0≤z → z≤δ →
--       (evenMoment mainMomentPower (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
--         (fun g => (conditionalGroupLaw H z g:ℂ))) ≤ Real.exp (-(4:ℝ)*k*Real.log s)) ∧
--       (evenMoment mainMomentPower (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
--         (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) ≤ Real.exp (-(4:ℝ)*k*Real.log s))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BinaryCoordinateSweeps.FreeSlot`, `OAI.BinaryCoordinateSweeps.GridSlot`, `OAI.BinaryCoordinateSweeps.PathFamily`, `OAI.BinaryCoordinateSweeps.conditionalGroupLaw`, `OAI.BinaryCoordinateSweeps.freeSlotFintype`, `OAI.BinaryCoordinateSweeps.gridSize`, `OAI.BinaryCoordinateSweeps.linePerturbationRadius`, `OAI.BinaryCoordinateSweeps.mainMomentPower`, `OAI.BinaryCoordinateSweeps.Irrep.evenMoment`, `OAI.BinaryCoordinateSweeps.Irrep.groupAverage`, `OAI.BinaryCoordinateSweeps.Young.Cell`, `OAI.BinaryCoordinateSweeps.Young.G`, `OAI.BinaryCoordinateSweeps.Young.SpechtHilbert`, `OAI.BinaryCoordinateSweeps.Young.Tabloid`, `OAI.BinaryCoordinateSweeps.Young.Tail`, `OAI.BinaryCoordinateSweeps.Young.hilbertInner`, `OAI.BinaryCoordinateSweeps.Young.hilbertNormed`, `OAI.BinaryCoordinateSweeps.Young.hilbertSpecht` and `OAI.BinaryCoordinateSweeps.Young.instFintypeElemForallCellNatTabloid` (definitions bundle `OAIB3Bs000` of this split); `OAI.BinaryCoordinateSweeps.Slot` and `OAI.BinaryCoordinateSweeps.realSign` (the published bundle `Def_BinarySweep`).
--
--   **Used by.** The proof of `OAI.BinaryCoordinateSweeps.real_grid_bound` of this split imports it.
-- source:
--   OpenAI, Row–column symmetry and contraction of coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BinarySweep/SparseBounds/ManySparse.lean (declaration OAI.BinaryCoordinateSweeps.sparse_uniform_radius)

import Mathlib
import Definitions.Def_BinarySweep
import Definitions.Def_OAIB3Bs000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Sparse Young Irrep

theorem sparse_uniform_radius : ∃ S : ℕ, ∀ r : ℕ, 2 ≤ r →
    4000000000 ≤ (r:ℝ)*Real.log 2 →
    ∃ δ : ℝ, 0<δ ∧ δ≤linePerturbationRadius r ∧ ∀ s : ℕ, S ≤ s →
    ∀ b h k : ℕ, ∀bits : Fin b → ℕ, gridSize bits=s → 1≤b →
    (∀j,r≤bits j ∧ bits j≤2*r) → (10:ℝ)^26≤Real.log s → 1≤k →
    ((k+h:ℕ):ℝ)≤(s:ℝ)^(1599/1600:ℝ) → h≤100000*k →
    ∀H : PathFamily bits h, ∀μ : YoungDiagram, ∀e : Cell μ ≃ FreeSlot H 0,
    ∀_a : Tail μ ≃ Fin k, ∀z : ℝ, 0≤z → z≤δ →
    (evenMoment mainMomentPower (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) ≤ Real.exp (-(4:ℝ)*k*Real.log s)) ∧
    (evenMoment mainMomentPower (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) ≤ Real.exp (-(4:ℝ)*k*Real.log s)) := by
  sorry

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

end

end OAI
end
