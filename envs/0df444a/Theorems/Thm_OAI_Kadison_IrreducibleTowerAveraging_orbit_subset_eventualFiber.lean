-- Prove2me | Theorems.Thm_OAI_Kadison_IrreducibleTowerAveraging_orbit_subset_eventualFiber
-- name    : OAI.Kadison.IrreducibleTowerAveraging.orbit_subset_eventualFiber
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:55:30.57029+00:00
-- url     : https://prove2.me/theorems/a301c6dd-f037-4dc9-b1a3-39c0256afa30
-- title:
--   OAI.Kadison.IrreducibleTowerAveraging.orbit_subset_eventualFiber: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.IrreducibleTowerAveraging`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology`, `open Filter`, `open TracialGNS NormalGNS MatrixExpectation`):
--
--   ```lean
--   lemma orbit_subset_eventualFiber (a : M) :
--       orbit M τ stage hmono a ⊆ eventualFiber M τ stage a
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.IrreducibleTowerAveraging.eventualFiber` and `OAI.Kadison.IrreducibleTowerAveraging.orbit` (definitions bundle `OAIQ039C038` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.IrreducibleTowerAveraging.expectation_tendsto` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C038

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

include hτ in
omit [∀ n, Nonempty (ι n)] in
lemma orbit_subset_eventualFiber (a : M) :
    orbit M τ stage hmono a ⊆ eventualFiber M τ stage a := by
  sorry

end Kadison.IrreducibleTowerAveraging

end

end OAI
end
