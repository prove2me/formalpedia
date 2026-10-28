-- Prove2me | Theorems.Thm_OAI_Heisenberg_field_local_small
-- name    : OAI.Heisenberg.field_local_small
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T08:31:35.355723+00:00
-- url     : https://prove2.me/theorems/3d666ee5-1f9b-47a7-96a8-a5d770eea2e1
-- title:
--   OAI.Heisenberg.field_local_small: intermediate lemma from OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Heisenberg.field_local_small` of [lean/OAI/MathematicalPhysics/Heisenberg/SpinFieldUniform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinFieldUniform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Heisenberg`, with `open scoped Classical BigOperators ComplexConjugate`, `open Filter Topology`):
--
--   ```lean
--   lemma field_local_small (F : Finset (Site d)) (B : QuasiLocal d ℓ)
--       (hB : B∈localAlgebra d ℓ (F : Set (Site d))) (K : Set ℝ) (hK : IsCompact K)
--       {ε : ℝ} (hε : 0<ε) : ∃ δ : ℝ,0<δ ∧ ∀ Γ : Finset (Site d),F⊆Γ →
--         ∀ h : ℝ,|h|<δ → ∀ t∈K,
--           dist (GibbsStrip.evolve (shiftedField Γ h) t B) (finiteDynamics d ℓ Γ t B)<ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.GibbsStrip.evolve`, `OAI.Heisenberg.localAlgebra`, `OAI.Heisenberg.quasiLocalClosed`, `OAI.Heisenberg.quasiLocalStarRing` and `OAI.Heisenberg.shiftedField` (definitions bundle `OAIW2HM000` of this split); `OAI.Heisenberg.Configuration`, `OAI.Heisenberg.QuasiLocal`, `OAI.Heisenberg.Site`, `OAI.Heisenberg.SpinHilbert`, `OAI.Heisenberg.SpinOperator` and `OAI.Heisenberg.finiteDynamics` (the published bundle `Def_Heisenberg`).
--
--   **Used by.** The proof of `OAI.Heisenberg.cubeAverage_limit_KMS` of this split imports it.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinFieldUniform.lean (declaration OAI.Heisenberg.field_local_small)

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM000

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

lemma field_local_small (F : Finset (Site d)) (B : QuasiLocal d ℓ)
    (hB : B∈localAlgebra d ℓ (F : Set (Site d))) (K : Set ℝ) (hK : IsCompact K)
    {ε : ℝ} (hε : 0<ε) : ∃ δ : ℝ,0<δ ∧ ∀ Γ : Finset (Site d),F⊆Γ →
      ∀ h : ℝ,|h|<δ → ∀ t∈K,
        dist (GibbsStrip.evolve (shiftedField Γ h) t B) (finiteDynamics d ℓ Γ t B)<ε := by
  sorry

end Heisenberg
end
end

end OAI
end
