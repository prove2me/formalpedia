-- Prove2me | Theorems.Thm_OAI_Kadison_NormalRepresentation_link_intertwines
-- name    : OAI.Kadison.NormalRepresentation.link_intertwines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:42:22.894474+00:00
-- url     : https://prove2.me/theorems/9d90243b-1997-4ca9-b46d-64e113edd976
-- title:
--   OAI.Kadison.NormalRepresentation.link_intertwines: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.NormalRepresentation`, with `open scoped ComplexOrder InnerProductSpace Topology`, `open HilbertBiprod PartialIsometryOrder BiprodLinkColumn OperatorAmplification`):
--
--   ```lean
--   lemma link_intertwines (v : Intertwiner (diagonalAlgebra M τ hnormal).commutant) (a : M) :
--       (component _ v).comp (a:H →L[ℂ] H)=(τ.gnsStarAlgHom a).comp (component _ v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertBiprod.Space` (definitions bundle `OAIQ039C000` of this split); `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.BiprodLinkColumn.Intertwiner` and `OAI.Kadison.BiprodLinkColumn.component` (definitions bundle `OAIQ039C020` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.NormalRepresentation.diagonalAlgebra` (definitions bundle `OAIQ039C062` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.NormalRepresentation.exists_countable_gns_embedding` and `OAI.Kadison.NormalRepresentation.finiteColumn_intertwines` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C062

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder BiprodLinkColumn OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hnormal : NormalGNS.BoundedWOTContinuous M τ)

lemma link_intertwines (v : Intertwiner (diagonalAlgebra M τ hnormal).commutant) (a : M) :
    (component _ v).comp (a:H →L[ℂ] H)=(τ.gnsStarAlgHom a).comp (component _ v) := by
  sorry

end Kadison.NormalRepresentation

end

end
end

end OAI
end
