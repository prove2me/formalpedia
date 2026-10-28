-- Prove2me | Theorems.Thm_OAI_Heisenberg_finite_cube_gibbs_strip
-- name    : OAI.Heisenberg.finite_cube_gibbs_strip
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T08:34:29.71458+00:00
-- url     : https://prove2.me/theorems/99583105-33d6-4b63-9e3f-cdaeb7ef2cbe
-- title:
--   OAI.Heisenberg.finite_cube_gibbs_strip: intermediate lemma from OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Heisenberg.finite_cube_gibbs_strip` of [lean/OAI/MathematicalPhysics/Heisenberg/SpinAveragedKMS.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinAveragedKMS.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Heisenberg`, with `open scoped Classical BigOperators ComplexConjugate`, `open Filter Topology`):
--
--   ```lean
--   lemma finite_cube_gibbs_strip (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (h : ℝ)
--       (τ : State d ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
--       {β : ℝ} (hβ : 0<β) (A B : QuasiLocal d ℓ) :
--       ∃ F : ℂ → ℂ,DiffContOnCl ℂ F (HeisenbergStrip.openStrip β) ∧
--         (∀ z∈HeisenbergStrip.closedStrip β,‖F z‖≤4*‖A‖*‖B‖) ∧
--         (∀ t : ℝ,F t=cubeBoundary Λ (gibbsState τ (shiftedField Λ h) β) h
--           (ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ) A) B t) ∧
--         (∀ t : ℝ,F ((t:ℂ)+Complex.I*β)=cubeBoundary Λ (gibbsState τ (shiftedField Λ h) β) h
--           ((ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ)).flip A) B t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Heisenberg.cubeBoundary`, `OAI.Heisenberg.quasiLocalClosed`, `OAI.Heisenberg.quasiLocalNormedRing`, `OAI.Heisenberg.shiftedField`, `OAI.HeisenbergStrip.closedStrip` and `OAI.HeisenbergStrip.openStrip` (definitions bundle `OAIW2HM000` of this split); `OAI.Heisenberg.gibbsState` (definitions bundle `OAIW2HM002` of this split); `OAI.Heisenberg.Configuration`, `OAI.Heisenberg.QuasiLocal`, `OAI.Heisenberg.Site`, `OAI.Heisenberg.SpinHilbert`, `OAI.Heisenberg.SpinOperator` and `OAI.Heisenberg.State` (the published bundle `Def_Heisenberg`).
--
--   **Used by.** The proof of `OAI.Heisenberg.cubeAverage_limit_KMS` of this split imports it.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinAveragedKMS.lean (declaration OAI.Heisenberg.finite_cube_gibbs_strip)

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

lemma finite_cube_gibbs_strip (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (h : ℝ)
    (τ : State d ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    {β : ℝ} (hβ : 0<β) (A B : QuasiLocal d ℓ) :
    ∃ F : ℂ → ℂ,DiffContOnCl ℂ F (HeisenbergStrip.openStrip β) ∧
      (∀ z∈HeisenbergStrip.closedStrip β,‖F z‖≤4*‖A‖*‖B‖) ∧
      (∀ t : ℝ,F t=cubeBoundary Λ (gibbsState τ (shiftedField Λ h) β) h
        (ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ) A) B t) ∧
      (∀ t : ℝ,F ((t:ℂ)+Complex.I*β)=cubeBoundary Λ (gibbsState τ (shiftedField Λ h) β) h
        ((ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ)).flip A) B t) := by
  sorry

end Heisenberg
end
end

end OAI
end
