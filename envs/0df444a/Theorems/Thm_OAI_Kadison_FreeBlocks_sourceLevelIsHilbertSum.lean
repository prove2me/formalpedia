-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_sourceLevelIsHilbertSum
-- name    : OAI.Kadison.FreeBlocks.sourceLevelIsHilbertSum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T07:04:25.359991+00:00
-- url     : https://prove2.me/theorems/4bc32901-5c7f-4863-bb96-c2c641a093ef
-- title:
--   OAI.Kadison.FreeBlocks.sourceLevelIsHilbertSum: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped ComplexOrder InnerProductSpace`, `open Complex ContinuousLinearMap UniformSpace Completion`, `open scoped InnerProductSpace`, `open scoped TensorProduct`, `open scoped TensorProduct InnerProductSpace Topology`, `open UniformSpace Completion Filter`, `open scoped TensorProduct`, `open UniformSpace Completion`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`, `open scoped InnerProductSpace TensorProduct ComplexOrder`, `open UniformSpace`, `open scoped InnerProductSpace _root_.Topology`, `open scoped TensorProduct`, `open UniformSpace`, `open scoped TensorProduct InnerProductSpace`, `open FreeWordTensor UniformSpace PreHilbert`, `open scoped ComplexOrder InnerProductSpace TensorProduct`):
--
--   ```lean
--   lemma sourceLevelIsHilbertSum : IsHilbertSum ℂ (sourceLevel t f hf S j)
--       (sourceLevelEmbedding t f hf S i j hS hfree hij)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.PreHilbert`, `OAI.Kadison.PreHilbert.power` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FreeBlocks.multiplicityLevel`, `OAI.Kadison.FreeBlocks.multiplicityTensor`, `OAI.Kadison.FreeBlocks.pullbackState` and `OAI.Kadison.FreeWordTensor.generatedOperators` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.factorFull`, `OAI.Kadison.FreeBlocks.factorZero`, `OAI.Kadison.FreeBlocks.sourceLevel`, `OAI.Kadison.FreeBlocks.sourceLevelEmbedding` and `OAI.Kadison.FreeBlocks.sourceScalar` (definitions bundle `OAIQ039C056` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.free_word_structure` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C056

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace PreHilbert

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : FreeMoments.Free S t.functional.toLinearMap) (hij : i≠j)

variable (hcolors : ∀ c : ι, c=i ∨ c=j)

variable (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

include hcolors hgen in
lemma sourceLevelIsHilbertSum : IsHilbertSum ℂ (sourceLevel t f hf S j)
    (sourceLevelEmbedding t f hf S i j hS hfree hij) := by
  sorry

end Kadison.FreeBlocks
end

end OAI
end
