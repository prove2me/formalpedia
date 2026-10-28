-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_free_word_structure
-- name    : OAI.Kadison.FreeBlocks.free_word_structure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:37:04.839042+00:00
-- url     : https://prove2.me/theorems/3c4980bd-2027-43ad-b969-bab58fe9b636
-- title:
--   OAI.Kadison.FreeBlocks.free_word_structure: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped ComplexOrder InnerProductSpace TensorProduct`, `open UniformSpace`, `open FreeWordTensor FreeMoments FreeWordAction`):
--
--   ```lean
--   theorem free_word_structure : ∃ B : ∀ k, multiplicityLevel t S j k →L[ℂ] multiplicityLevel t S j k,
--       (∀ k, ‖B k‖ ≤ ‖G‖) ∧
--       (∀ k (d : factorFull t f hf)
--         (x : factorZero t f hf) (a : multiplicityLevel t S j k),
--         G (embeddedSourceWord t f hf S i j hS hfree hij k d x a) =
--           embeddedSourceWord t f hf S i j hS hfree hij k d x (B k a)) ∧
--       (∀ k (d : factorFull t f hf)
--         (x : factorZero t f hf) (a : multiplicityLevel t S j k),
--         G.adjoint (embeddedSourceWord t f hf S i j hS hfree hij k d x a) =
--           embeddedSourceWord t f hf S i j hS hfree hij k d x ((B k).adjoint a))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.PreHilbert` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialGNS.stageAlgebra` and `OAI.Kadison.TracialGNS.stageUnitary` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.FreeBlocks.multiplicityLevel`, `OAI.Kadison.FreeBlocks.multiplicityTensor` and `OAI.Kadison.FreeWordTensor.generatedOperators` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.factorTrace` (definitions bundle `OAIQ039C046` of this split); `OAI.Kadison.FreeBlocks.factorFull` and `OAI.Kadison.FreeBlocks.factorZero` (definitions bundle `OAIQ039C056` of this split); `OAI.Kadison.FreeBlocks.innerRepresentation` (definitions bundle `OAIQ039C059` of this split); `OAI.Kadison.FreeBlocks.embeddedSourceWord` (definitions bundle `OAIQ039C063` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.stage_hankel_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C059
import Definitions.Def_OAIQ039C063

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (hij : i≠j) (hcolors : ∀ c : ι, c=i ∨ c=j)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hDgen : ∀ a : D, (factorTrace t f hf).gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer
    (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (hGL : ∀ a : D, G.comp (t.functional.gnsStarAlgHom (f a))=
  (t.functional.gnsStarAlgHom (f a)).comp G)

variable (hGW : ∀ n u, G.comp
  (innerRepresentation t ht f S i hS hfree hgen (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap =
  (innerRepresentation t ht f S i hS hfree hgen (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap.comp G)

include hgen hcolors he hsize hDgen hGL hGW in
theorem free_word_structure : ∃ B : ∀ k, multiplicityLevel t S j k →L[ℂ] multiplicityLevel t S j k,
    (∀ k, ‖B k‖ ≤ ‖G‖) ∧
    (∀ k (d : factorFull t f hf)
      (x : factorZero t f hf) (a : multiplicityLevel t S j k),
      G (embeddedSourceWord t f hf S i j hS hfree hij k d x a) =
        embeddedSourceWord t f hf S i j hS hfree hij k d x (B k a)) ∧
    (∀ k (d : factorFull t f hf)
      (x : factorZero t f hf) (a : multiplicityLevel t S j k),
      G.adjoint (embeddedSourceWord t f hf S i j hS hfree hij k d x a) =
        embeddedSourceWord t f hf S i j hS hfree hij k d x ((B k).adjoint a)) := by
  sorry

end Kadison.FreeBlocks

end

end OAI
end
