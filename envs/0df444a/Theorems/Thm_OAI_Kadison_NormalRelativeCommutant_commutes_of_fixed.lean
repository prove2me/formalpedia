-- Prove2me | Theorems.Thm_OAI_Kadison_NormalRelativeCommutant_commutes_of_fixed
-- name    : OAI.Kadison.NormalRelativeCommutant.commutes_of_fixed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:22:39.037389+00:00
-- url     : https://prove2.me/theorems/28ff3d94-471e-465d-a730-94e70be7a676
-- title:
--   OAI.Kadison.NormalRelativeCommutant.commutes_of_fixed: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.NormalRelativeCommutant`, with `open scoped InnerProductSpace ComplexOrder`, `open TracialGNS NormalGNS`):
--
--   ```lean
--   lemma commutes_of_fixed (b : M) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
--       (hfix : ∀ u : unitary D,
--         conjugation τ hτ (liftedUnitary M π u) (algebraVector τ b)=algebraVector τ b) :
--       ∀ a : D, π a*b=b*π a
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.TracialGNS.algebraVector` and `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.TracialGNS.conjugation` (definitions bundle `OAIQ039C032` of this split); `OAI.Kadison.NormalRelativeCommutant.liftedUnitary` (definitions bundle `OAIQ039C040` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.IrreducibleTowerAveraging.scalar_mem_hull` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C040

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

open scoped InnerProductSpace ComplexOrder

namespace Kadison.NormalRelativeCommutant

open TracialGNS NormalGNS

variable {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra D]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (π : D →⋆ₐ[ℂ] M)

lemma commutes_of_fixed (b : M) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfix : ∀ u : unitary D,
      conjugation τ hτ (liftedUnitary M π u) (algebraVector τ b)=algebraVector τ b) :
    ∀ a : D, π a*b=b*π a := by
  sorry

end Kadison.NormalRelativeCommutant

end

end
end

end OAI
end
