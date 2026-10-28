-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_norm_base_mul
-- name    : OAI.Kadison.FreeBlocks.norm_base_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:58:45.919644+00:00
-- url     : https://prove2.me/theorems/8893fc02-0c8e-4cb5-b421-e3bea23d7460
-- title:
--   OAI.Kadison.FreeBlocks.norm_base_mul: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped InnerProductSpace TensorProduct ComplexOrder`, `open UniformSpace`, `open FreeMoments FreeWordTensor`):
--
--   ```lean
--   lemma norm_base_mul (s : letterSpace t S j) (hs : ‖s‖=1)
--       (x : letterSpace t S i) (d : D) (v : multiplicityLevel t S j 0) :
--       ‖t.functional.gnsStarAlgHom (f d) (blockEmbedding t S hfree hij 0 v)‖=
--         ‖TracialGNS.algebraVector (factorTrace t f hf) d‖*‖v‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.algebraVector` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.faithfulNormed`, `OAI.Kadison.FreeWordTensor.letterSpace`, `OAI.Kadison.FreeWordTensor.preSpace` and `OAI.Kadison.FreeWordTensor.Space` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FreeBlocks.blockTensor` and `OAI.Kadison.FreeBlocks.factorSpace` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FreeBlocks.multiplicityLevel`, `OAI.Kadison.FreeBlocks.multiplicityTensor` and `OAI.Kadison.FreeBlocks.pullbackState` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.factorTrace` (definitions bundle `OAIQ039C046` of this split); `OAI.Kadison.FreeBlocks.blockEmbedding` (definitions bundle `OAIQ039C047` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.propagation_of_local_module` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C046
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

include hS in
lemma norm_base_mul (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (d : D) (v : multiplicityLevel t S j 0) :
    ‖t.functional.gnsStarAlgHom (f d) (blockEmbedding t S hfree hij 0 v)‖=
      ‖TracialGNS.algebraVector (factorTrace t f hf) d‖*‖v‖ := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
