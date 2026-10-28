-- Prove2me | Theorems.Thm_OAI_Heisenberg_Selection_field_ordered_cubes
-- name    : OAI.Heisenberg.Selection.field_ordered_cubes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T08:31:49.558731+00:00
-- url     : https://prove2.me/theorems/c5475096-71db-4932-a7ab-479af0c789c6
-- title:
--   OAI.Heisenberg.Selection.field_ordered_cubes: intermediate lemma from OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Heisenberg.Selection.field_ordered_cubes` of [lean/OAI/MathematicalPhysics/Heisenberg/CubeSelection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/CubeSelection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Heisenberg.Selection`, with `open scoped Classical BigOperators Fin.NatCast Matrix Matrix.Norms.Operator`, `open Filter Topology`, `open Heisenberg.Geometry SpatialFrame SlotTensor`):
--
--   ```lean
--   theorem field_ordered_cubes (d ℓ : ℕ) (hd : 2≤d) [NeZero ℓ]
--       (τ : State (d+1) ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A)) :
--       ∃ β₀ : ℝ,0<β₀ ∧ ∀ β : ℝ,β₀≤β → ∀ h : ℝ,0<h →
--         ∀ᶠ n : ℕ in atTop,
--           ((box (d+1) (n+1)).card:ℝ)*ℓ/8≤
--             ((gibbsState τ (shiftedField (box (d+1) (n+1)) h) β).functional
--               (totalZ (box (d+1) (n+1)))).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Heisenberg.shiftedField` and `OAI.Heisenberg.totalZ` (definitions bundle `OAIW2HM000` of this split); `OAI.Heisenberg.gibbsState` (definitions bundle `OAIW2HM002` of this split); `OAI.Heisenberg.Configuration`, `OAI.Heisenberg.QuasiLocal`, `OAI.Heisenberg.Site`, `OAI.Heisenberg.SpinHilbert`, `OAI.Heisenberg.SpinOperator`, `OAI.Heisenberg.State` and `OAI.Heisenberg.box` (the published bundle `Def_Heisenberg`).
--
--   **Used by.** The proof of `OAI.Heisenberg.spontaneous_magnetization` of this split imports it.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/CubeSelection.lean (declaration OAI.Heisenberg.Selection.field_ordered_cubes)

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Fin.NatCast Matrix Matrix.Norms.Operator
open Filter Topology
namespace Heisenberg.Selection
open Heisenberg.Geometry SpatialFrame SlotTensor

theorem field_ordered_cubes (d ℓ : ℕ) (hd : 2≤d) [NeZero ℓ]
    (τ : State (d+1) ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A)) :
    ∃ β₀ : ℝ,0<β₀ ∧ ∀ β : ℝ,β₀≤β → ∀ h : ℝ,0<h →
      ∀ᶠ n : ℕ in atTop,
        ((box (d+1) (n+1)).card:ℝ)*ℓ/8≤
          ((gibbsState τ (shiftedField (box (d+1) (n+1)) h) β).functional
            (totalZ (box (d+1) (n+1)))).re := by
  sorry

end Heisenberg.Selection
end
end

end OAI
end
