-- Prove2me | Theorems.Thm_OAI_Heisenberg_cubeBoundary_upper
-- name    : OAI.Heisenberg.cubeBoundary_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T08:29:17.497976+00:00
-- url     : https://prove2.me/theorems/b48b920f-1981-4553-8332-32510aaa4a57
-- title:
--   OAI.Heisenberg.cubeBoundary_upper: intermediate lemma from OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Heisenberg.cubeBoundary_upper` of [lean/OAI/MathematicalPhysics/Heisenberg/SpinAveragedKMS.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinAveragedKMS.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Heisenberg`, with `open scoped Classical BigOperators ComplexConjugate`, `open Filter Topology`):
--
--   ```lean
--   lemma cubeBoundary_upper (Λ : Finset (Site d)) (ω : State d ℓ) (h : ℝ)
--       (A B : QuasiLocal d ℓ) (t : ℝ) :
--       cubeBoundary Λ ω h ((ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ)).flip A) B t=
--         (Λ.card:ℂ)⁻¹*∑ x∈Λ,ω.functional (GibbsStrip.evolve (shiftedField Λ h) t (translation d ℓ x B)*translation d ℓ x A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.GibbsStrip.evolve`, `OAI.Heisenberg.cubeBoundary`, `OAI.Heisenberg.quasiLocalClosed` and `OAI.Heisenberg.shiftedField` (definitions bundle `OAIW2HM000` of this split); `OAI.Heisenberg.Configuration`, `OAI.Heisenberg.QuasiLocal`, `OAI.Heisenberg.Site`, `OAI.Heisenberg.SpinHilbert`, `OAI.Heisenberg.SpinOperator`, `OAI.Heisenberg.State` and `OAI.Heisenberg.translation` (the published bundle `Def_Heisenberg`).
--
--   **Used by.** The proof of `OAI.Heisenberg.finite_cube_gibbs_strip` of this split imports it.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinAveragedKMS.lean (declaration OAI.Heisenberg.cubeBoundary_upper)

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

lemma cubeBoundary_upper (Λ : Finset (Site d)) (ω : State d ℓ) (h : ℝ)
    (A B : QuasiLocal d ℓ) (t : ℝ) :
    cubeBoundary Λ ω h ((ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ)).flip A) B t=
      (Λ.card:ℂ)⁻¹*∑ x∈Λ,ω.functional (GibbsStrip.evolve (shiftedField Λ h) t (translation d ℓ x B)*translation d ℓ x A) := by
  sorry

end Heisenberg
end
end

end OAI
end
