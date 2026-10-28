-- Prove2me | Theorems.Thm_OAI_Kadison_NormalRepresentation_right_mem_commutant
-- name    : OAI.Kadison.NormalRepresentation.right_mem_commutant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:43:01.825226+00:00
-- url     : https://prove2.me/theorems/f899e01f-01e0-4153-ae52-3c9b7f177460
-- title:
--   OAI.Kadison.NormalRepresentation.right_mem_commutant: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.NormalRepresentation`, with `open scoped ComplexOrder InnerProductSpace Topology`, `open HilbertBiprod PartialIsometryOrder`):
--
--   ```lean
--   lemma right_mem_commutant (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
--       right (H:=H) (G:=τ.GNS)∈(diagonalAlgebra M τ hnormal).commutant
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertBiprod.Space` (definitions bundle `OAIQ039C000` of this split); `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.HilbertBiprod.right` (definitions bundle `OAIQ039C020` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.NormalRepresentation.diagonalAlgebra` (definitions bundle `OAIQ039C062` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.NormalRepresentation.exists_orthogonal_links` and `OAI.Kadison.NormalRepresentation.exists_orthogonal_links_of_faithful` of this split import it.
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

open HilbertBiprod PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma right_mem_commutant (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    right (H:=H) (G:=τ.GNS)∈(diagonalAlgebra M τ hnormal).commutant := by
  sorry

end Kadison.NormalRepresentation

end

end
end

end OAI
end
