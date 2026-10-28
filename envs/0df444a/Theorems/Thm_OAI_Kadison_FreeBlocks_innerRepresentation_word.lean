-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_innerRepresentation_word
-- name    : OAI.Kadison.FreeBlocks.innerRepresentation_word
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:37:19.037991+00:00
-- url     : https://prove2.me/theorems/6c7f2000-9508-4cb1-b1de-5509025f6336
-- title:
--   OAI.Kadison.FreeBlocks.innerRepresentation_word: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped ComplexOrder InnerProductSpace TensorProduct`, `open UniformSpace`, `open FreeWordTensor FreeMoments FreeWordAction`):
--
--   ```lean
--   lemma innerRepresentation_word (u : unitary D) (d : D) (n : ℕ)
--       (x : BlockParams t S i j n) :
--       innerRepresentation t ht f S i hS hfree hgen u
--         (sourceLevelEmbedding t f hf S i j hS hfree hij n
--           (levelWord t f hf S i j hS d n x)) =
--       sourceLevelEmbedding t f hf S i j hS hfree hij n
--         (levelWord t f hf S i j hS ((u:D)*d*star (u:D)) n
--           (mapBlockD t S i j
--             (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
--               (innerFamily_trace t ht f i u) i) n x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.letterSpace`, `OAI.Kadison.FreeWordTensor.preSpace`, `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FreeWordAction.innerFamily` and `OAI.Kadison.FreeWordAction.innerFamily_mem` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.FreeBlocks.BlockParams` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FreeBlocks.multiplicityLevel`, `OAI.Kadison.FreeBlocks.multiplicityTensor`, `OAI.Kadison.FreeBlocks.pullbackState` and `OAI.Kadison.FreeWordTensor.generatedOperators` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeWordAction.innerFamily_trace` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.FreeWordAction.letterIso` (definitions bundle `OAIQ039C046` of this split); `OAI.Kadison.FreeBlocks.factorFull`, `OAI.Kadison.FreeBlocks.factorZero`, `OAI.Kadison.FreeBlocks.levelWord`, `OAI.Kadison.FreeBlocks.mapBlockD`, `OAI.Kadison.FreeBlocks.sourceLevel`, `OAI.Kadison.FreeBlocks.sourceLevelEmbedding` and `OAI.Kadison.FreeBlocks.sourceScalar` (definitions bundle `OAIQ039C056` of this split); `OAI.Kadison.FreeBlocks.innerRepresentation` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.free_word_structure` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C059

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

variable (hij : i≠j)

lemma innerRepresentation_word (u : unitary D) (d : D) (n : ℕ)
    (x : BlockParams t S i j n) :
    innerRepresentation t ht f S i hS hfree hgen u
      (sourceLevelEmbedding t f hf S i j hS hfree hij n
        (levelWord t f hf S i j hS d n x)) =
    sourceLevelEmbedding t f hf S i j hS hfree hij n
      (levelWord t f hf S i j hS ((u:D)*d*star (u:D)) n
        (mapBlockD t S i j
          (letterIso t S (innerFamily f i u) (innerFamily_mem f S i hS u)
            (innerFamily_trace t ht f i u) i) n x)) := by
  sorry

end Kadison.FreeBlocks

end

end OAI
end
