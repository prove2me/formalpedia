-- Prove2me | Theorems.Thm_OAI_Kadison_NormalGNS_separable_gns
-- name    : OAI.Kadison.NormalGNS.separable_gns
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:46:19.362678+00:00
-- url     : https://prove2.me/theorems/0f2dd6d3-d555-4b5c-851d-0b564e71f4fa
-- title:
--   OAI.Kadison.NormalGNS.separable_gns: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.NormalGNS`, with `open Filter`, `open scoped InnerProductSpace Topology NNReal ComplexOrder`, `open TracialGNS`):
--
--   ```lean
--   theorem separable_gns [TopologicalSpace.SeparableSpace H]
--       (hnormal : BoundedWOTContinuous M τ) : TopologicalSpace.SeparableSpace τ.GNS
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.NormalRepresentation.exists_countable_gns_embedding` and `OAI.Kadison.NormalRepresentation.separable_traced_factor_bound` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C022

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

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open Filter

open scoped InnerProductSpace Topology NNReal ComplexOrder

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

theorem separable_gns [TopologicalSpace.SeparableSpace H]
    (hnormal : BoundedWOTContinuous M τ) : TopologicalSpace.SeparableSpace τ.GNS := by
  sorry

end Kadison.NormalGNS

end

end
end

end OAI
end
