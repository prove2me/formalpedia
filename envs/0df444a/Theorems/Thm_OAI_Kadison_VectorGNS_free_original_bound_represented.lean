-- Prove2me | Theorems.Thm_OAI_Kadison_VectorGNS_free_original_bound_represented
-- name    : OAI.Kadison.VectorGNS.free_original_bound_represented
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:47:12.953497+00:00
-- url     : https://prove2.me/theorems/7e3972d4-febd-4196-bf2c-d6818d387951
-- title:
--   OAI.Kadison.VectorGNS.free_original_bound_represented: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.VectorGNS`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator`, `open FreeWordTensor FreeWordAction FreeMoments FreeBlocks`):
--
--   ```lean
--   theorem free_original_bound_represented
--       (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
--       (τ : B →ₚ[ℂ] ℂ) (j : B →⋆ₐ[ℂ] M) (htrace : ∀ a,τ a=subalgebraTrace M ξ (j a))
--       (hj : ∀ a : B,j a∈R true)
--       (U : H →L[ℂ] H) (T : τ.GNS →L[ℂ] τ.GNS)
--       (hGT : ∀ x,subalgebraCompression M ξ U
--         (originalEmbedding τ (vectorState M ξ hfaith hone) j htrace x)=
--         originalEmbedding τ (vectorState M ξ hfaith hone) j htrace (T x))
--       (hGD : ∀ d : D,U*(d:H →L[ℂ] H)=(d:H →L[ℂ] H)*U)
--       (s : unitary B) (hs0 : τ (s:B)=0) (hs2 : (s:B)*(s:B)=1)
--       {c β : ℝ} (hc : 0 ≤ c) (hβ : 0<β) (hβ1 : β≤1)
--       (hC : RepresentedCornerBound M ξ D U c (β:ℂ)) :
--       ‖T*τ.gnsStarAlgHom (s:B)-τ.gnsStarAlgHom (s:B)*T‖≤1040*c
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.FreeMoments.Free` and `OAI.Kadison.FreeWordTensor.FaithfulState` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.VectorGNS.subalgebraTrace` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.VectorGNS.subalgebraCompression` (definitions bundle `OAIQ039C052` of this split); `OAI.Kadison.FreeBlocks.originalEmbedding` (definitions bundle `OAIQ039C056` of this split); `OAI.Kadison.VectorGNS.inclusion` (definitions bundle `OAIQ039C060` of this split); `OAI.Kadison.VectorGNS.GeneratedByStages` (definitions bundle `OAIQ039C064` of this split); `OAI.Kadison.VectorGNS.RepresentedCornerBound` and `OAI.Kadison.VectorGNS.vectorState` (definitions bundle `OAIQ039C065` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.free_position_small_corners_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C060
import Definitions.Def_OAIQ039C064
import Definitions.Def_OAIQ039C065

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.VectorGNS

open FreeWordTensor FreeWordAction FreeMoments FreeBlocks

variable {H B : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

variable (D : VonNeumannAlgebra H) (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)
  (R : Bool → StarSubalgebra ℂ M) (hR : R false=(inclusion M D hDM).range)
  (hfree : Free R (subalgebraTrace M ξ).toLinearMap)
  (hgen : ∀ a : M,(a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
    (((iSup R).map M.toStarSubalgebra.subtype) : Set (H →L[ℂ] H))))

variable (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ},n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a,φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : GeneratedByStages D ξ I φ)

include htr hR hfree hgen hinc hsize hDgen in
theorem free_original_bound_represented
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (τ : B →ₚ[ℂ] ℂ) (j : B →⋆ₐ[ℂ] M) (htrace : ∀ a,τ a=subalgebraTrace M ξ (j a))
    (hj : ∀ a : B,j a∈R true)
    (U : H →L[ℂ] H) (T : τ.GNS →L[ℂ] τ.GNS)
    (hGT : ∀ x,subalgebraCompression M ξ U
      (originalEmbedding τ (vectorState M ξ hfaith hone) j htrace x)=
      originalEmbedding τ (vectorState M ξ hfaith hone) j htrace (T x))
    (hGD : ∀ d : D,U*(d:H →L[ℂ] H)=(d:H →L[ℂ] H)*U)
    (s : unitary B) (hs0 : τ (s:B)=0) (hs2 : (s:B)*(s:B)=1)
    {c β : ℝ} (hc : 0 ≤ c) (hβ : 0<β) (hβ1 : β≤1)
    (hC : RepresentedCornerBound M ξ D U c (β:ℂ)) :
    ‖T*τ.gnsStarAlgHom (s:B)-τ.gnsStarAlgHom (s:B)*T‖≤1040*c := by
  sorry

end Kadison.VectorGNS

end

end
end

end OAI
end
