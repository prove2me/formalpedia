-- Prove2me | Theorems.Thm_OAI_Kadison_CornerPhase_exists_relative_corner_phase
-- name    : OAI.Kadison.CornerPhase.exists_relative_corner_phase
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:33:01.324213+00:00
-- url     : https://prove2.me/theorems/962efc7f-2c9c-4645-a3ff-ce6a6f0ad944
-- title:
--   OAI.Kadison.CornerPhase.exists_relative_corner_phase: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CornerPhase`, with `open scoped ComplexOrder BigOperators InnerProductSpace`):
--
--   ```lean
--   theorem exists_relative_corner_phase {J : Type*} [Fintype J]
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
--       (hN : DiffuseProjection.HasNoMinimalProjections N)
--       (q : M) (hq : IsStarProjection q) (hqN : (q : H →L[ℂ] H)∈N)
--       (hqt : 0<(τ q).re)
--       (a : J → M) (k : J → ℕ) (hk : ∀ j,0<k j) {ε : ℝ} (hε : 0<ε) :
--       ∃ u : M, star u*u=q ∧ u*star u=q ∧ u*q=u ∧ q*u=u ∧ ‖u‖ ≤ 1 ∧
--         (∀ j, ‖τ (u^k j*a j)‖<ε*(τ q).re) ∧ (u : H →L[ℂ] H)∈N
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` (definitions bundle `OAIQ039C008` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.exists_finite_word_patch` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.CornerPhase

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M N : VonNeumannAlgebra H) (hNM : N ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ hNM in
theorem exists_relative_corner_phase {J : Type*} [Fintype J]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (hN : DiffuseProjection.HasNoMinimalProjections N)
    (q : M) (hq : IsStarProjection q) (hqN : (q : H →L[ℂ] H)∈N)
    (hqt : 0<(τ q).re)
    (a : J → M) (k : J → ℕ) (hk : ∀ j,0<k j) {ε : ℝ} (hε : 0<ε) :
    ∃ u : M, star u*u=q ∧ u*star u=q ∧ u*q=u ∧ q*u=u ∧ ‖u‖ ≤ 1 ∧
      (∀ j, ‖τ (u^k j*a j)‖<ε*(τ q).re) ∧ (u : H →L[ℂ] H)∈N := by
  sorry

end Kadison.CornerPhase

end

end
end

end OAI
end
