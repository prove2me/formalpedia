-- Prove2me | Theorems.Thm_OAI_Kadison_NormalRepresentation_diagonal_factor
-- name    : OAI.Kadison.NormalRepresentation.diagonal_factor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:41:07.826896+00:00
-- url     : https://prove2.me/theorems/0853f781-350a-4e27-ab46-fcb58e730b89
-- title:
--   OAI.Kadison.NormalRepresentation.diagonal_factor: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.NormalRepresentation`, with `open scoped ComplexOrder InnerProductSpace Topology`, `open HilbertBiprod PartialIsometryOrder`):
--
--   ```lean
--   lemma diagonal_factor (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hM : FactorCorner.IsFactor M) : FactorCorner.IsFactor (diagonalAlgebra M τ hnormal)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertBiprod.Space` (definitions bundle `OAIQ039C000` of this split); `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.NormalRepresentation.diagonalAlgebra` (definitions bundle `OAIQ039C062` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.NormalRepresentation.exists_orthogonal_links` of this split imports it.
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

lemma diagonal_factor (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hM : FactorCorner.IsFactor M) : FactorCorner.IsFactor (diagonalAlgebra M τ hnormal) := by
  sorry

end Kadison.NormalRepresentation

end

end
end

end OAI
end
