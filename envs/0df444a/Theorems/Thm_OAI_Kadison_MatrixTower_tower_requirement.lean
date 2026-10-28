-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixTower_tower_requirement
-- name    : OAI.Kadison.MatrixTower.tower_requirement
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:07:05.477129+00:00
-- url     : https://prove2.me/theorems/9dff4f52-995b-4046-8785-bb3909262c20
-- title:
--   OAI.Kadison.MatrixTower.tower_requirement: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixTower`, with `open scoped ComplexOrder BigOperators InnerProductSpace`, `open TracialGNS MatrixExpectation`):
--
--   ```lean
--   lemma tower_requirement (j : ℕ) {ε : ℝ} (hε : 0<ε) : ∃ n,
--       ‖algebraVector τ (expectation (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n).hom
--         (x j)-τ (x j) • (1:M))‖<ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.TracialGNS.algebraVector` and `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.MatrixExpectation.expectation` (definitions bundle `OAIQ039C012` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.MatrixTower.tower` (definitions bundle `OAIQ039C075` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.exists_irreducible_stage_tower` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C075

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

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixTower

open TracialGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [instance] Stage.finite Stage.dec Stage.nonempty

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hnormal : NormalGNS.BoundedWOTContinuous M τ)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
  (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)

variable (x : ℕ → M) (hx : ∀ j,IsSelfAdjoint (x j))

lemma tower_requirement (j : ℕ) {ε : ℝ} (hε : 0<ε) : ∃ n,
    ‖algebraVector τ (expectation (tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx n).hom
      (x j)-τ (x j) • (1:M))‖<ε := by
  sorry

end Kadison.MatrixTower

end

end
end

end OAI
end
