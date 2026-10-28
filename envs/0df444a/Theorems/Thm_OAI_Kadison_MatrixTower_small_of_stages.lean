-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixTower_small_of_stages
-- name    : OAI.Kadison.MatrixTower.small_of_stages
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T07:02:31.833563+00:00
-- url     : https://prove2.me/theorems/cf7c89a9-6d25-4b52-8fa1-c67621a8a3a1
-- title:
--   OAI.Kadison.MatrixTower.small_of_stages: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixTower`, with `open scoped ComplexOrder`):
--
--   ```lean
--   lemma small_of_stages (F : ℕ → Stage M)
--       (hsize : ∀ N : ℕ,∃ n,N<Fintype.card (F n).I) {ε : ℝ} (hε : 0<ε) :
--       ∃ q : M,IsStarProjection q ∧ q≠0 ∧ (τ q).re<ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.MatrixTower.Stage` (definitions bundle `OAIQ039C054` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.OperatorAmplification.matrix_diffuse_of_stages` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
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

open scoped ComplexOrder

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)

include hτ hone in
lemma small_of_stages (F : ℕ → Stage M)
    (hsize : ∀ N : ℕ,∃ n,N<Fintype.card (F n).I) {ε : ℝ} (hε : 0<ε) :
    ∃ q : M,IsStarProjection q ∧ q≠0 ∧ (τ q).re<ε := by
  sorry

end Kadison.MatrixTower

end

end
end

end OAI
end
