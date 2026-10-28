-- Prove2me | Theorems.Thm_OAI_Heisenberg_cubeAverage_limit_KMS
-- name    : OAI.Heisenberg.cubeAverage_limit_KMS
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T08:33:46.962508+00:00
-- url     : https://prove2.me/theorems/450e9557-b80b-4e1f-9d37-5b3fa2604664
-- title:
--   OAI.Heisenberg.cubeAverage_limit_KMS: intermediate lemma from OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Heisenberg.cubeAverage_limit_KMS` of [lean/OAI/MathematicalPhysics/Heisenberg/SpinAveragedKMS.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinAveragedKMS.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Heisenberg`, with `open scoped Classical BigOperators ComplexConjugate`, `open Filter Topology`):
--
--   ```lean
--   theorem cubeAverage_limit_KMS (τ : State d ℓ)
--       (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
--       {β : ℝ} (hβ : 0<β) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
--       (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (ω : State d ℓ)
--       (hω : ∀ A,Tendsto (fun n=>(cubeAverage (box d (N n)) (box_nonempty d (N n))
--         (gibbsState τ (shiftedField (box d (N n)) (h n)) β)).functional A) atTop (𝓝 (ω.functional A))) : IsKMS β ω
--   ```
--
--   **Definitions.** The statement is written with `OAI.Heisenberg.box_nonempty`, `OAI.Heisenberg.cubeAverage` and `OAI.Heisenberg.shiftedField` (definitions bundle `OAIW2HM000` of this split); `OAI.Heisenberg.gibbsState` (definitions bundle `OAIW2HM002` of this split); `OAI.Heisenberg.Configuration`, `OAI.Heisenberg.IsKMS`, `OAI.Heisenberg.QuasiLocal`, `OAI.Heisenberg.SpinHilbert`, `OAI.Heisenberg.SpinOperator`, `OAI.Heisenberg.State` and `OAI.Heisenberg.box` (the published bundle `Def_Heisenberg`).
--
--   **Used by.** The proof of `OAI.Heisenberg.spontaneous_magnetization` of this split imports it.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinAveragedKMS.lean (declaration OAI.Heisenberg.cubeAverage_limit_KMS)

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
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

theorem cubeAverage_limit_KMS (τ : State d ℓ)
    (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    {β : ℝ} (hβ : 0<β) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (ω : State d ℓ)
    (hω : ∀ A,Tendsto (fun n=>(cubeAverage (box d (N n)) (box_nonempty d (N n))
      (gibbsState τ (shiftedField (box d (N n)) (h n)) β)).functional A) atTop (𝓝 (ω.functional A))) : IsKMS β ω := by
  sorry

end Heisenberg
end
end

end OAI
end
