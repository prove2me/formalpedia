-- Prove2me | Theorems.Thm_OAI_Kadison_IrreducibleTowerAveraging_expectation_tendsto
-- name    : OAI.Kadison.IrreducibleTowerAveraging.expectation_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:43:52.179996+00:00
-- url     : https://prove2.me/theorems/240cbddf-2124-4aa5-80be-dba57c47fa9c
-- title:
--   OAI.Kadison.IrreducibleTowerAveraging.expectation_tendsto: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.IrreducibleTowerAveraging`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology`, `open Filter`, `open TracialGNS NormalGNS MatrixExpectation`):
--
--   ```lean
--   theorem expectation_tendsto
--       (hnormal : BoundedWOTContinuous M τ)
--       (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
--       (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
--         ∃ c : ℂ, b=algebraMap ℂ M c)
--       (a : M) (ha : ‖a‖≤1) :
--       Tendsto (fun n => algebraVector τ (expectation (stage n) a)) atTop
--         (𝓝 ((τ a) • vacuum τ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.TracialGNS.algebraVector`, `OAI.Kadison.TracialGNS.vacuum` and `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.MatrixExpectation.expectation` (definitions bundle `OAIQ039C012` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.LocalQuantization.exists_centered_compression` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C012
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.IrreducibleTowerAveraging

open TracialGNS NormalGNS MatrixExpectation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

include hτ hmono in
theorem expectation_tendsto
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : M) (ha : ‖a‖≤1) :
    Tendsto (fun n => algebraVector τ (expectation (stage n) a)) atTop
      (𝓝 ((τ a) • vacuum τ)) := by
  sorry

end Kadison.IrreducibleTowerAveraging

end

end OAI
end
