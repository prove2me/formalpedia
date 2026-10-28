-- Prove2me | Theorems.Thm_OAI_Kadison_CornerSymmetrization_bound_small_projection
-- name    : OAI.Kadison.CornerSymmetrization.bound_small_projection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:34.077982+00:00
-- url     : https://prove2.me/theorems/ce9a3113-885c-4879-8f8a-d7b107c5e67f
-- title:
--   OAI.Kadison.CornerSymmetrization.bound_small_projection: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CornerSymmetrization`, with `open scoped ComplexOrder InnerProductSpace`):
--
--   ```lean
--   theorem bound_small_projection (M : VonNeumannAlgebra H)
--       (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
--       (hone : τ 1=1) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
--       (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (P : StarSubalgebra ℂ (K →L[ℂ] K))
--       (Ω : K) (hΩ : ∀ a : M, vectorState Ω (π a)=τ a)
--       (G : K →L[ℂ] K) (ε β : ℝ) (hβ : β≤1)
--       (hbound : ∀ x, CornerElement π.range P Ω (β:ℂ) x → ‖G*x-x*G‖≤ε*‖x‖)
--       (q : M) (hq : IsStarProjection q) (hqt : (τ q).re≤β)
--       (x : K →L[ℂ] K) (hx : x∈P) (hl : π q*x=x) (hr : x*π q=x) :
--       ‖G*x-x*G‖≤ε*‖x‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.CornerSymmetrization.CornerElement` and `OAI.Kadison.CornerSymmetrization.vectorState` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.normal_free_corner_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.CornerSymmetrization

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem bound_small_projection (M : VonNeumannAlgebra H)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hone : τ 1=1) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (P : StarSubalgebra ℂ (K →L[ℂ] K))
    (Ω : K) (hΩ : ∀ a : M, vectorState Ω (π a)=τ a)
    (G : K →L[ℂ] K) (ε β : ℝ) (hβ : β≤1)
    (hbound : ∀ x, CornerElement π.range P Ω (β:ℂ) x → ‖G*x-x*G‖≤ε*‖x‖)
    (q : M) (hq : IsStarProjection q) (hqt : (τ q).re≤β)
    (x : K →L[ℂ] K) (hx : x∈P) (hl : π q*x=x) (hr : x*π q=x) :
    ‖G*x-x*G‖≤ε*‖x‖ := by
  sorry

end Kadison.CornerSymmetrization

end

end
end

end OAI
end
