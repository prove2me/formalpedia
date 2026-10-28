-- Prove2me | Theorems.Thm_OAI_CoordinateSweeps_Grid_Holes_conditional_sparse_main
-- name    : OAI.CoordinateSweeps.Grid.Holes.conditional_sparse_main
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:30:17.260457+00:00
-- url     : https://prove2.me/theorems/7b9901e1-00a7-47da-ad6b-671334f1d66b
-- title:
--   OAI.CoordinateSweeps.Grid.Holes.conditional_sparse_main: intermediate lemma from OpenAI, Conditional information under deterministic coordinate sweeps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoordinateSweeps.all_grid_moment` and `OAI.CoordinateSweeps.conditional_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Conditional information under deterministic coordinate sweeps*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoordinateSweeps.Grid.Holes.conditional_sparse_main` of [lean/OAI/Probability/CoordinateSweeps/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CoordinateSweeps/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoordinateSweeps.Grid.Holes`, with `open scoped Matrix.Norms.L2Operator`, `open SparseScalar ScalarInduction`):
--
--   ```lean
--   theorem conditional_sparse_main (hr : ScaleLarge r) (hrS : ScaleReady r)
--       (hG : G.Allowed r) (hS : MainSizeReady SparseScalar.q G.size)
--       (hf : H.Feasible) {zStar : ℝ} (hζ : SparsePerturb r zStar) {z : ℝ} (hz : z∈Set.Icc 0 zStar)
--       (σ : UnitaryIrrep H.stabilizer) (hσ : σ.dimension≠1)
--       (ha : ¬ (1+c G.size)*Real.log σ.dimension ≤ e G.size*h*Real.log G.size-H.cost)
--       (hF : Real.log σ.dimension < (G.size:ℝ)^(1-a/4)) :
--       schattenMoment SparseScalar.q (H.conditionalAverage hf z σ) ≤
--         Real.exp (-c G.size*Real.log σ.dimension+e G.size*h*Real.log G.size-H.cost)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoordinateSweeps.Grid`, `OAI.CoordinateSweeps.ScaleLarge`, `OAI.CoordinateSweeps.SparsePerturb`, `OAI.CoordinateSweeps.UnitaryIrrep`, `OAI.CoordinateSweeps.a`, `OAI.CoordinateSweeps.c`, `OAI.CoordinateSweeps.e`, `OAI.CoordinateSweeps.schattenMoment`, `OAI.CoordinateSweeps.Grid.Allowed`, `OAI.CoordinateSweeps.Grid.Holes`, `OAI.CoordinateSweeps.Grid.Slot`, `OAI.CoordinateSweeps.Grid.size`, `OAI.CoordinateSweeps.ScalarInduction.MainSizeReady`, `OAI.CoordinateSweeps.SparseScalar.ScaleReady`, `OAI.CoordinateSweeps.SparseScalar.q`, `OAI.CoordinateSweeps.Grid.Holes.Feasible`, `OAI.CoordinateSweeps.Grid.Holes.conditionalAverage`, `OAI.CoordinateSweeps.Grid.Holes.cost` and `OAI.CoordinateSweeps.Grid.Holes.stabilizer` (the published bundle `Def_CoordinateSweeps`).
--
--   **Used by.** The proof of `OAI.CoordinateSweeps.all_grid_moment` of this split imports it.
-- source:
--   OpenAI, Conditional information under deterministic coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Conditional-information-under-deterministic-coordinate-sweeps-September-26-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CoordinateSweeps/Main.lean (declaration OAI.CoordinateSweeps.Grid.Holes.conditional_sparse_main)

import Mathlib
import Definitions.Def_CoordinateSweeps

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps.Grid.Holes
open SparseScalar ScalarInduction
variable {G : Grid} {h r : ℕ} (H : G.Holes h)
theorem conditional_sparse_main (hr : ScaleLarge r) (hrS : ScaleReady r)
    (hG : G.Allowed r) (hS : MainSizeReady SparseScalar.q G.size)
    (hf : H.Feasible) {zStar : ℝ} (hζ : SparsePerturb r zStar) {z : ℝ} (hz : z∈Set.Icc 0 zStar)
    (σ : UnitaryIrrep H.stabilizer) (hσ : σ.dimension≠1)
    (ha : ¬ (1+c G.size)*Real.log σ.dimension ≤ e G.size*h*Real.log G.size-H.cost)
    (hF : Real.log σ.dimension < (G.size:ℝ)^(1-a/4)) :
    schattenMoment SparseScalar.q (H.conditionalAverage hf z σ) ≤
      Real.exp (-c G.size*Real.log σ.dimension+e G.size*h*Real.log G.size-H.cost) := by
  sorry
end CoordinateSweeps.Grid.Holes

end OAI
end
