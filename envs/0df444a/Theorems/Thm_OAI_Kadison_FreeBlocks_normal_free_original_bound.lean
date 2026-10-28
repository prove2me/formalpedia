-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_normal_free_original_bound
-- name    : OAI.Kadison.FreeBlocks.normal_free_original_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:26:26.2687+00:00
-- url     : https://prove2.me/theorems/ce3d914e-f3e1-4b1b-91a9-278fd758c629
-- title:
--   OAI.Kadison.FreeBlocks.normal_free_original_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator`, `open FreeMoments FreeWordTensor FreeWordAction`):
--
--   ```lean
--   theorem normal_free_original_bound
--       (hnormal : NormalGNS.BoundedWOTContinuous D (factorTrace t f hf))
--       (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
--       (τ : B →ₚ[ℂ] ℂ) (j : B →⋆ₐ[ℂ] A) (htrace : ∀ a,τ a=t.functional (j a))
--       (hj : ∀ a : B,j a∈R true)
--       (G : t.functional.GNS →L[ℂ] t.functional.GNS) (T : τ.GNS →L[ℂ] τ.GNS)
--       (hGT : ∀ x,G (originalEmbedding τ t j htrace x)=originalEmbedding τ t j htrace (T x))
--       (hGD : ∀ a : D,G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)
--       (s : unitary B) (hs0 : τ (s:B)=0) (hs2 : (s:B)*(s:B)=1)
--       (ε β : ℝ) (hε : 0≤ε) (hβ : 0<β) (hβ1 : β≤1)
--       (hC : ∀ x,CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t R)
--         (TracialGNS.vacuum t.functional) (β:ℂ) x → ‖G*x-x*G‖≤ε*‖x‖) :
--       ‖T*τ.gnsStarAlgHom (s:B)-τ.gnsStarAlgHom (s:B)*T‖≤1040*ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.TracialGNS.vacuum` and `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.CornerSymmetrization.CornerElement` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.FreeMoments.Free` and `OAI.Kadison.FreeWordTensor.FaithfulState` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialGNS.stageAlgebra` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.FreeWordTensor.generatedOperators` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.factorTrace` (definitions bundle `OAIQ039C046` of this split); `OAI.Kadison.FreeBlocks.ambientOperators` and `OAI.Kadison.FreeBlocks.factorOperators` (definitions bundle `OAIQ039C055` of this split); `OAI.Kadison.FreeBlocks.originalEmbedding` (definitions bundle `OAIQ039C056` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.VectorGNS.free_original_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C055
import Definitions.Def_OAIQ039C056

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

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeWordAction

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (D : VonNeumannAlgebra H)
  (t : FaithfulState A) (htr : ∀ a b : A,t.functional (a*b)=t.functional (b*a))
  (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)
  (R : Bool → StarSubalgebra ℂ A) (hR : R false=f.range)
  (hfree : Free R t.functional.toLinearMap)
  (hgen : ∀ a : A,t.functional.gnsStarAlgHom a∈
    Set.centralizer (Set.centralizer (generatedOperators t R : Set _)))
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ},n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a,φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : ∀ a : D,(factorTrace t f hf).gnsStarAlgHom a∈
    Set.centralizer (Set.centralizer (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

include htr hR hfree hgen hinc hsize hDgen in
theorem normal_free_original_bound
    (hnormal : NormalGNS.BoundedWOTContinuous D (factorTrace t f hf))
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (τ : B →ₚ[ℂ] ℂ) (j : B →⋆ₐ[ℂ] A) (htrace : ∀ a,τ a=t.functional (j a))
    (hj : ∀ a : B,j a∈R true)
    (G : t.functional.GNS →L[ℂ] t.functional.GNS) (T : τ.GNS →L[ℂ] τ.GNS)
    (hGT : ∀ x,G (originalEmbedding τ t j htrace x)=originalEmbedding τ t j htrace (T x))
    (hGD : ∀ a : D,G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)
    (s : unitary B) (hs0 : τ (s:B)=0) (hs2 : (s:B)*(s:B)=1)
    (ε β : ℝ) (hε : 0≤ε) (hβ : 0<β) (hβ1 : β≤1)
    (hC : ∀ x,CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t R)
      (TracialGNS.vacuum t.functional) (β:ℂ) x → ‖G*x-x*G‖≤ε*‖x‖) :
    ‖T*τ.gnsStarAlgHom (s:B)-τ.gnsStarAlgHom (s:B)*T‖≤1040*ε := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
