-- Prove2me | Theorems.Thm_OAI_Kadison_CornerTransport_finite_small_corner_bound
-- name    : OAI.Kadison.CornerTransport.finite_small_corner_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:18.003375+00:00
-- url     : https://prove2.me/theorems/c724d86d-6dec-46c5-a303-3d0c972c6ddb
-- title:
--   OAI.Kadison.CornerTransport.finite_small_corner_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CornerTransport`, with `open scoped ComplexOrder`):
--
--   ```lean
--   theorem finite_small_corner_bound (Q : VonNeumannAlgebra H) (hQ : FactorCorner.IsFactor Q)
--       (σ : Q →ₚ[ℂ] ℂ) (hσ : ∀ a b : Q,σ (a*b)=σ (b*a))
--       (hfaith : ∀ a : Q,σ (star a*a)=0 → a=0)
--       (j : Q →⋆ₐ[ℂ] A) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
--       (T : K →L[ℂ] K) (hT : ∀ q : Q,T*ρ (j q)=ρ (j q)*T)
--       (e : Q) (he : IsStarProjection e) {c : ℝ}
--       (hbound : ∀ z : A,j e*z*j e=z → ‖T*ρ z-ρ z*T‖ ≤ c*‖z‖)
--       (f : Q) (hf : IsStarProjection f) (htrace : σ f≤σ e)
--       (z : A) (hz : j f*z*j f=z) : ‖T*ρ z-ρ z*T‖ ≤ c*‖z‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.OperatorAmplification.matrix_small_corner_bound` of this split imports it.
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

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder

namespace Kadison.CornerTransport

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem finite_small_corner_bound (Q : VonNeumannAlgebra H) (hQ : FactorCorner.IsFactor Q)
    (σ : Q →ₚ[ℂ] ℂ) (hσ : ∀ a b : Q,σ (a*b)=σ (b*a))
    (hfaith : ∀ a : Q,σ (star a*a)=0 → a=0)
    (j : Q →⋆ₐ[ℂ] A) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (T : K →L[ℂ] K) (hT : ∀ q : Q,T*ρ (j q)=ρ (j q)*T)
    (e : Q) (he : IsStarProjection e) {c : ℝ}
    (hbound : ∀ z : A,j e*z*j e=z → ‖T*ρ z-ρ z*T‖ ≤ c*‖z‖)
    (f : Q) (hf : IsStarProjection f) (htrace : σ f≤σ e)
    (z : A) (hz : j f*z*j f=z) : ‖T*ρ z-ρ z*T‖ ≤ c*‖z‖ := by
  sorry

end Kadison.CornerTransport

end

end
end

end OAI
end
