-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixTower_scalar_of_commutes
-- name    : OAI.Kadison.MatrixTower.scalar_of_commutes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T07:02:12.83041+00:00
-- url     : https://prove2.me/theorems/d5ba47dc-f7f3-4f58-b0bc-72c0350972bc
-- title:
--   OAI.Kadison.MatrixTower.scalar_of_commutes: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixTower`, with `open scoped ComplexOrder BigOperators InnerProductSpace ComplexStarModule`, `open TracialGNS MatrixExpectation`):
--
--   ```lean
--   theorem scalar_of_commutes (a : M)
--       (hc : ∀ n b,(F n).hom b*a=a*(F n).hom b) : a=τ a • (1:M)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.TracialGNS.algebraVector` and `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.MatrixExpectation.expectation` (definitions bundle `OAIQ039C012` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.exists_irreducible_stage_tower` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C012
import Definitions.Def_OAIQ039C054

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

open scoped ComplexOrder BigOperators InnerProductSpace ComplexStarModule

namespace Kadison.MatrixTower

open TracialGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hone : τ 1=1)

variable (x : ℕ → M)
  (hxden : ∀ a : M,IsSelfAdjoint a → ∀ ε : ℝ,0<ε → ∃ j,‖algebraVector τ (a-x j)‖<ε)
  (F : ℕ → Stage M)
  (hreq : ∀ j : ℕ,∀ ε : ℝ,0<ε → ∃ n,
    ‖algebraVector τ (expectation (F n).hom (x j)-τ (x j) • (1:M))‖<ε)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)

include hτ hone hxden hreq hfaith in
theorem scalar_of_commutes (a : M)
    (hc : ∀ n b,(F n).hom b*a=a*(F n).hom b) : a=τ a • (1:M) := by
  sorry

end Kadison.MatrixTower

end

end
end

end OAI
end
