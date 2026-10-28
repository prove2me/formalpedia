-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixModule_endpoint_unit_bound
-- name    : OAI.Kadison.MatrixModule.endpoint_unit_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:08:33.514755+00:00
-- url     : https://prove2.me/theorems/c8173d57-0fc6-4470-9610-316f538b2340
-- title:
--   OAI.Kadison.MatrixModule.endpoint_unit_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixModule`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`):
--
--   ```lean
--   lemma endpoint_unit_bound
--       (Y : Completion (E ⊗[ℂ] F) →L[ℂ] Completion (E ⊗[ℂ] G))
--       (hY : ∀ a, Y.comp (HilbertTensor.map (ρ a) (1 : F →L[ℂ] F)) =
--         (HilbertTensor.map (ρ a) (1 : G →L[ℂ] G)).comp Y)
--       (i j : I) (x : F) (z : G) :
--       ‖inner ℂ ((ρ (Matrix.single i j 1) Ω ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)
--         (Y ((Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _))‖ ≤
--         ‖Y‖ * (Fintype.card I : ℝ)⁻¹ * ‖x‖ * ‖z‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertTensor.map` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.normalizedTrace` (definitions bundle `OAIQ039C019` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialGNS.stageCoefficient_rank_one` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C011
import Definitions.Def_OAIQ039C019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion

namespace Kadison

variable {I : Type*} [Fintype I] [DecidableEq I]

namespace MatrixModule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable (ρ : Matrix I I ℂ →⋆ₐ[ℂ] (E →L[ℂ] E)) (Ω : E)
  (htrace : ∀ a, inner ℂ Ω (ρ a Ω) = normalizedTrace a)

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

include htrace in
lemma endpoint_unit_bound
    (Y : Completion (E ⊗[ℂ] F) →L[ℂ] Completion (E ⊗[ℂ] G))
    (hY : ∀ a, Y.comp (HilbertTensor.map (ρ a) (1 : F →L[ℂ] F)) =
      (HilbertTensor.map (ρ a) (1 : G →L[ℂ] G)).comp Y)
    (i j : I) (x : F) (z : G) :
    ‖inner ℂ ((ρ (Matrix.single i j 1) Ω ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)
      (Y ((Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _))‖ ≤
      ‖Y‖ * (Fintype.card I : ℝ)⁻¹ * ‖x‖ * ‖z‖ := by
  sorry

end MatrixModule

end Kadison
end

end OAI
end
