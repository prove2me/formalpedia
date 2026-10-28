-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixCornerImplementation_exists_matrix_corner_intertwiner
-- name    : OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:45:31.863328+00:00
-- url     : https://prove2.me/theorems/88290112-0106-432f-97eb-e8071b4b0b5a
-- title:
--   OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixCornerImplementation`, with `open scoped InnerProductSpace`, `open ContinuousLinearMap`, `open MatrixCornerHilbert ReducingRepresentation ConcreteCorner`):
--
--   ```lean
--   theorem exists_matrix_corner_intertwiner (v : ι → Algebra M)
--       (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
--       (hinit : ∀ i, p*star (v i)=star (v i))
--       (htotal : ∑ i, v i*star (v i)=1)
--       (hGv : ∀ i x, G (σ (v i) x)=inclusion M (v i) (G x))
--       (Ω : K) (hΩ : DenseRange (fun a : Algebra M => σ a Ω)) (hpΩ : σ p Ω=Ω)
--       {ε : ℝ} (hε : 0≤ε)
--       (hδ : ∀ a : Corner hp, ‖G.comp (σ (a:Algebra M))-(inclusion M (a:Algebra M)).comp G‖≤ε*‖a‖) :
--       ∃ T : K →L[ℂ] H, (∀ a : Algebra M, T.comp (σ a)=(inclusion M a).comp T) ∧
--         ‖G-T‖≤16*ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.ConcreteCorner.Algebra` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.Corner`, `OAI.Kadison.cornerSubalgebra`, `OAI.Kadison.instNormedRingCorner` and `OAI.Kadison.ConcreteCorner.closedCarrier` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.ConcreteCorner.inclusion` (definitions bundle `OAIQ039C020` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixCornerImplementation.exists_local_module` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C004
import Definitions.Def_OAIQ039C020

section

attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.MatrixCornerImplementation

open MatrixCornerHilbert ReducingRepresentation ConcreteCorner

variable {H K ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Fintype ι] [DecidableEq ι]

variable (M : VonNeumannAlgebra H)
  (σ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (j : K →ₗᵢ[ℂ] H)
  (hj : ∀ a x, j (σ a x)=inclusion M a (j x))

variable {p : Algebra M} (hp : IsStarProjection p)

variable (G : K →L[ℂ] H) (hGp : ∀ x, G (σ p x)=inclusion M p (G x))

include hj hGp in
theorem exists_matrix_corner_intertwiner (v : ι → Algebra M)
    (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
    (hinit : ∀ i, p*star (v i)=star (v i))
    (htotal : ∑ i, v i*star (v i)=1)
    (hGv : ∀ i x, G (σ (v i) x)=inclusion M (v i) (G x))
    (Ω : K) (hΩ : DenseRange (fun a : Algebra M => σ a Ω)) (hpΩ : σ p Ω=Ω)
    {ε : ℝ} (hε : 0≤ε)
    (hδ : ∀ a : Corner hp, ‖G.comp (σ (a:Algebra M))-(inclusion M (a:Algebra M)).comp G‖≤ε*‖a‖) :
    ∃ T : K →L[ℂ] H, (∀ a : Algebra M, T.comp (σ a)=(inclusion M a).comp T) ∧
      ‖G-T‖≤16*ε := by
  sorry

end Kadison.MatrixCornerImplementation

end

end
end

end OAI
end
