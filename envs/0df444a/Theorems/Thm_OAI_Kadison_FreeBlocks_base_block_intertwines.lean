-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_base_block_intertwines
-- name    : OAI.Kadison.FreeBlocks.base_block_intertwines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:33:58.171864+00:00
-- url     : https://prove2.me/theorems/0691591f-2c9c-42e9-84c5-ee6973d43947
-- title:
--   OAI.Kadison.FreeBlocks.base_block_intertwines: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open UniformSpace`, `open scoped InnerProductSpace ComplexOrder`, `open ContinuousLinearMap`, `open FreeWordTensor FreeMoments DihedralCorner`):
--
--   ```lean
--   lemma base_block_intertwines
--       (G : t.functional.GNS →L[ℂ] t.functional.GNS)
--       (B : ∀ k, multiplicityLevel t S true k →L[ℂ] multiplicityLevel t S true k)
--       (hb : ∀ k a (x : letterSpace t S false) v,
--         G (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k v)=
--           repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k (B k v))
--       (sl : letterSpace t S true) (sn : ‖sl‖=1) :
--       G.comp (baseEmbedding t S hfree).toContinuousLinearMap=
--         (baseEmbedding t S hfree).toContinuousLinearMap.comp (B 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.faithfulNormed`, `OAI.Kadison.FreeWordTensor.letterSpace`, `OAI.Kadison.FreeWordTensor.preSpace` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FreeBlocks.factorSpace` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FreeBlocks.multiplicityLevel` and `OAI.Kadison.FreeBlocks.multiplicityTensor` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.baseEmbedding` (definitions bundle `OAIQ039C055` of this split); `OAI.Kadison.FreeBlocks.repeatedOutput` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.base_block_compression` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C059

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments DihedralCorner

section Base

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)
  (hfree : Free S t.functional.toLinearMap)

lemma base_block_intertwines
    (G : t.functional.GNS →L[ℂ] t.functional.GNS)
    (B : ∀ k, multiplicityLevel t S true k →L[ℂ] multiplicityLevel t S true k)
    (hb : ∀ k a (x : letterSpace t S false) v,
      G (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k v)=
        repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k (B k v))
    (sl : letterSpace t S true) (sn : ‖sl‖=1) :
    G.comp (baseEmbedding t S hfree).toContinuousLinearMap=
      (baseEmbedding t S hfree).toContinuousLinearMap.comp (B 0) := by
  sorry

end Base

end Kadison.FreeBlocks

end

end
end

end OAI
end
