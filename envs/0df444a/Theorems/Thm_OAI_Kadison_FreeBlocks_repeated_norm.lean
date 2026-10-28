-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_repeated_norm
-- name    : OAI.Kadison.FreeBlocks.repeated_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:58:21.988171+00:00
-- url     : https://prove2.me/theorems/7120ab7c-cfea-4e68-9aae-d5eacb9d51ac
-- title:
--   OAI.Kadison.FreeBlocks.repeated_norm: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped InnerProductSpace TensorProduct ComplexOrder`, `open UniformSpace`, `open FreeMoments FreeWordTensor`):
--
--   ```lean
--   lemma repeated_norm (s : letterSpace t S j) (hs : ‖s‖=1)
--       (x : letterSpace t S i) (hx : ‖x‖=1) (n : ℕ) (v : multiplicityLevel t S j 0) :
--       ‖t.functional.gnsStarAlgHom ((letterValue t S j s*letterValue t S i x)^n)
--           (blockEmbedding t S hfree hij 0 v)‖=‖v‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.faithfulNormed`, `OAI.Kadison.FreeWordTensor.letterSpace`, `OAI.Kadison.FreeWordTensor.letterValue`, `OAI.Kadison.FreeWordTensor.preSpace` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FreeBlocks.blockTensor` and `OAI.Kadison.FreeBlocks.factorSpace` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FreeBlocks.multiplicityLevel` and `OAI.Kadison.FreeBlocks.multiplicityTensor` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.blockEmbedding` (definitions bundle `OAIQ039C047` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.propagation_of_local_module` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C047

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace TensorProduct ComplexOrder

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

include hf hS in
lemma repeated_norm (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (hx : ‖x‖=1) (n : ℕ) (v : multiplicityLevel t S j 0) :
    ‖t.functional.gnsStarAlgHom ((letterValue t S j s*letterValue t S i x)^n)
        (blockEmbedding t S hfree hij 0 v)‖=‖v‖ := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
