-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixTower_exists_irreducible_stage_tower
-- name    : OAI.Kadison.MatrixTower.exists_irreducible_stage_tower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T07:02:18.836237+00:00
-- url     : https://prove2.me/theorems/81686080-627f-46da-9941-1b2471d92a6d
-- title:
--   OAI.Kadison.MatrixTower.exists_irreducible_stage_tower: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixTower`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology`, `open Filter`, `open OperatorAmplification CyclicColumns`):
--
--   ```lean
--   theorem exists_irreducible_stage_tower [TopologicalSpace.SeparableSpace τ.GNS]
--       (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
--       (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
--       (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M) :
--       ∃ E : ℕ → Stage M, Monotone (fun n => (E n).hom.range) ∧
--         (∀ n,n+1 ≤ Fintype.card (E n).I) ∧
--         (∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.DiffuseProjection.HasNoMinimalProjections` and `OAI.Kadison.FactorCorner.IsFactor` (definitions bundle `OAIQ039C008` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.finite_standard_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C054

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification CyclicColumns

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M]

variable (τ : M →ₚ[ℂ] ℂ)

omit [Nontrivial M] in
theorem exists_irreducible_stage_tower [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M) :
    ∃ E : ℕ → Stage M, Monotone (fun n => (E n).hom.range) ∧
      (∀ n,n+1 ≤ Fintype.card (E n).I) ∧
      (∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M)) := by
  sorry

end Kadison.MatrixTower

end

end OAI
end
