-- Prove2me | Theorems.Thm_OAI_Kadison_CyclicSpatial_exists_embedded_cyclic_intertwiner
-- name    : OAI.Kadison.CyclicSpatial.exists_embedded_cyclic_intertwiner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:28:22.926571+00:00
-- url     : https://prove2.me/theorems/e6b10fc4-2529-40c3-8361-e8bb9472e675
-- title:
--   OAI.Kadison.CyclicSpatial.exists_embedded_cyclic_intertwiner: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CyclicSpatial`, with `open scoped InnerProductSpace`, `open ContinuousLinearMap`):
--
--   ```lean
--   theorem exists_embedded_cyclic_intertwiner (M : VonNeumannAlgebra H)
--       (hρ : Function.Injective ρ) (hrange : Set.range ρ=(M : Set (H →L[ℂ] H)))
--       (G : K →L[ℂ] H) (Ω : K) (hΩ : DenseRange (fun a : A => σ a Ω))
--       {ε : ℝ} (hε : 0≤ε)
--       (hδ : ∀ a : A, ‖G.comp (σ a)-(ρ a).comp G‖≤ε*‖a‖) :
--       ∃ T : K →L[ℂ] H, (∀ a : A,T.comp (σ a)=(ρ a).comp T) ∧ ‖G-T‖≤16*ε
--   ```
--
--   **Used by.** The proofs of `OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner` and `OAI_Kadison_MatrixCornerImplementation_exists_represented_local_module` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.CyclicSpatial

variable {A K H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
  (j : K →ₗᵢ[ℂ] H) (hj : ∀ a x, j (σ a x)=ρ a (j x))

include hj in
theorem exists_embedded_cyclic_intertwiner (M : VonNeumannAlgebra H)
    (hρ : Function.Injective ρ) (hrange : Set.range ρ=(M : Set (H →L[ℂ] H)))
    (G : K →L[ℂ] H) (Ω : K) (hΩ : DenseRange (fun a : A => σ a Ω))
    {ε : ℝ} (hε : 0≤ε)
    (hδ : ∀ a : A, ‖G.comp (σ a)-(ρ a).comp G‖≤ε*‖a‖) :
    ∃ T : K →L[ℂ] H, (∀ a : A,T.comp (σ a)=(ρ a).comp T) ∧ ‖G-T‖≤16*ε := by
  sorry

end Kadison.CyclicSpatial

end

end
end

end OAI
end
