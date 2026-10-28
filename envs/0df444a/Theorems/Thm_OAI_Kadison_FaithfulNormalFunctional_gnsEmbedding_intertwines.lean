-- Prove2me | Theorems.Thm_OAI_Kadison_FaithfulNormalFunctional_gnsEmbedding_intertwines
-- name    : OAI.Kadison.FaithfulNormalFunctional.gnsEmbedding_intertwines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:52:26.760859+00:00
-- url     : https://prove2.me/theorems/1282d304-2098-4908-8d63-1cf5512fca47
-- title:
--   OAI.Kadison.FaithfulNormalFunctional.gnsEmbedding_intertwines: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FaithfulNormalFunctional`, with `open scoped InnerProductSpace ComplexOrder Topology ENNReal`):
--
--   ```lean
--   lemma gnsEmbedding_intertwines (a : M) (v : (restricted x M).GNS) (n : ℕ) :
--       gnsEmbedding x M ((restricted x M).gnsStarAlgHom a v) n=a.val (gnsEmbedding x M v n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.InfiniteAmplification.Space` (definitions bundle `OAIQ039C006` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.FaithfulNormalFunctional.restricted` (definitions bundle `OAIQ039C024` of this split); `OAI.Kadison.FaithfulNormalFunctional.gnsEmbedding` (definitions bundle `OAIQ039C035` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.NormalRepresentation.exists_stable_gns_model` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C035

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

open scoped InnerProductSpace ComplexOrder Topology ENNReal

namespace Kadison.FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (x : ℕ → H)

variable (M : VonNeumannAlgebra H)

lemma gnsEmbedding_intertwines (a : M) (v : (restricted x M).GNS) (n : ℕ) :
    gnsEmbedding x M ((restricted x M).gnsStarAlgHom a v) n=a.val (gnsEmbedding x M v n) := by
  sorry

end Kadison.FaithfulNormalFunctional

end

end
end

end OAI
end
