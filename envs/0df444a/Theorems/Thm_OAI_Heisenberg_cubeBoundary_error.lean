-- Prove2me | Theorems.Thm_OAI_Heisenberg_cubeBoundary_error
-- name    : OAI.Heisenberg.cubeBoundary_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T08:31:08.669149+00:00
-- url     : https://prove2.me/theorems/143d6365-2b91-4b36-97cd-fdf5a6d3a626
-- title:
--   OAI.Heisenberg.cubeBoundary_error: intermediate lemma from OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Heisenberg.cubeBoundary_error` of [lean/OAI/MathematicalPhysics/Heisenberg/SpinAverageBoundary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinAverageBoundary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Heisenberg`, with `open scoped Classical BigOperators ComplexConjugate`, `open Filter Topology`):
--
--   ```lean
--   lemma cubeBoundary_error (N r : ℕ) (hr : r≤N) (ω : State d ℓ) (h t : ℝ)
--       (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ)
--       {δ : ℝ} (hδ : 0≤δ)
--       (hgood : ∀ Γ : Finset (Site d),box d r⊆Γ →
--         dist (GibbsStrip.evolve (shiftedField Γ h) t B) (dynamics d ℓ t B)≤δ) :
--       ‖cubeBoundary (box d N) ω h M B t-
--         (cubeAverage (box d N) (box_nonempty d N) ω).functional (M (dynamics d ℓ t B))‖≤
--           4*‖M‖*δ+(((box d N\box d (N-r)).card:ℝ)/(box d N).card)*(8*‖M‖*‖B‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.GibbsStrip.evolve`, `OAI.Heisenberg.box_nonempty`, `OAI.Heisenberg.cubeAverage`, `OAI.Heisenberg.cubeBoundary`, `OAI.Heisenberg.quasiLocalAddCommMonoid`, `OAI.Heisenberg.quasiLocalClosed`, `OAI.Heisenberg.quasiLocalModule`, `OAI.Heisenberg.quasiLocalNormedRing` and `OAI.Heisenberg.shiftedField` (definitions bundle `OAIW2HM000` of this split); `OAI.Heisenberg.Configuration`, `OAI.Heisenberg.QuasiLocal`, `OAI.Heisenberg.Site`, `OAI.Heisenberg.SpinHilbert`, `OAI.Heisenberg.SpinOperator`, `OAI.Heisenberg.State`, `OAI.Heisenberg.box` and `OAI.Heisenberg.dynamics` (the published bundle `Def_Heisenberg`).
--
--   **Used by.** The proof of `OAI.Heisenberg.cubeAverage_limit_KMS` of this split imports it.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/SpinAverageBoundary.lean (declaration OAI.Heisenberg.cubeBoundary_error)

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

lemma cubeBoundary_error (N r : ℕ) (hr : r≤N) (ω : State d ℓ) (h t : ℝ)
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ)
    {δ : ℝ} (hδ : 0≤δ)
    (hgood : ∀ Γ : Finset (Site d),box d r⊆Γ →
      dist (GibbsStrip.evolve (shiftedField Γ h) t B) (dynamics d ℓ t B)≤δ) :
    ‖cubeBoundary (box d N) ω h M B t-
      (cubeAverage (box d N) (box_nonempty d N) ω).functional (M (dynamics d ℓ t B))‖≤
        4*‖M‖*δ+(((box d N\box d (N-r)).card:ℝ)/(box d N).card)*(8*‖M‖*‖B‖) := by
  sorry

end Heisenberg
end
end

end OAI
end
