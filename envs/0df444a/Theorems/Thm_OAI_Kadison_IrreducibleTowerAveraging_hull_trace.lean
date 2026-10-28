-- Prove2me | Theorems.Thm_OAI_Kadison_IrreducibleTowerAveraging_hull_trace
-- name    : OAI.Kadison.IrreducibleTowerAveraging.hull_trace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:55:49.143214+00:00
-- url     : https://prove2.me/theorems/0ca6340a-46f0-43a9-9991-56acdf687433
-- title:
--   OAI.Kadison.IrreducibleTowerAveraging.hull_trace: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.IrreducibleTowerAveraging`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology`, `open Filter`, `open TracialGNS NormalGNS MatrixExpectation`):
--
--   ```lean
--   lemma hull_trace (a : M) :
--       ∀ x∈closedConvexHull ℝ (orbit M τ stage hmono a), inner ℂ (vacuum τ) x=τ a
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.TracialGNS.vacuum` and `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.IrreducibleTowerAveraging.orbit` (definitions bundle `OAIQ039C038` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.IrreducibleTowerAveraging.scalar_mem_hull` of this split imports it.
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
lemma hull_trace (a : M) :
    ∀ x∈closedConvexHull ℝ (orbit M τ stage hmono a), inner ℂ (vacuum τ) x=τ a := by
  sorry

end Kadison.IrreducibleTowerAveraging

end

end OAI
end
