-- Prove2me | Theorems.Thm_OAI_Heisenberg_state_limit_locallyUniform
-- name    : OAI.Heisenberg.state_limit_locallyUniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T08:30:02.284294+00:00
-- url     : https://prove2.me/theorems/ad8baab5-1291-418e-b7d9-0e8ca8cdebf1
-- title:
--   OAI.Heisenberg.state_limit_locallyUniform: intermediate lemma from OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Heisenberg.state_limit_locallyUniform` of [lean/OAI/MathematicalPhysics/Heisenberg/SpinAverageBoundary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinAverageBoundary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Heisenberg`, with `open scoped Classical BigOperators ComplexConjugate`, `open Filter Topology`):
--
--   ```lean
--   lemma state_limit_locallyUniform {η : ℕ → State d ℓ} {ω : State d ℓ}
--       (hη : ∀ A,Tendsto (fun n=>(η n).functional A) atTop (𝓝 (ω.functional A)))
--       (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ) :
--       TendstoLocallyUniformly (fun n t=>(η n).functional (M (dynamics d ℓ t B)))
--         (fun t=>ω.functional (M (dynamics d ℓ t B))) atTop
--   ```
--
--   **Definitions.** The statement is written with `OAI.Heisenberg.quasiLocalAddCommMonoid` and `OAI.Heisenberg.quasiLocalModule` (definitions bundle `OAIW2HM000` of this split); `OAI.Heisenberg.Configuration`, `OAI.Heisenberg.QuasiLocal`, `OAI.Heisenberg.SpinHilbert`, `OAI.Heisenberg.SpinOperator`, `OAI.Heisenberg.State` and `OAI.Heisenberg.dynamics` (the published bundle `Def_Heisenberg`).
--
--   **Used by.** The proof of `OAI.Heisenberg.cubeAverage_limit_KMS` of this split imports it.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinAverageBoundary.lean (declaration OAI.Heisenberg.state_limit_locallyUniform)

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

lemma state_limit_locallyUniform {η : ℕ → State d ℓ} {ω : State d ℓ}
    (hη : ∀ A,Tendsto (fun n=>(η n).functional A) atTop (𝓝 (ω.functional A)))
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ) :
    TendstoLocallyUniformly (fun n t=>(η n).functional (M (dynamics d ℓ t B)))
      (fun t=>ω.functional (M (dynamics d ℓ t B))) atTop := by
  sorry

end Heisenberg
end
end

end OAI
end
