-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_admissible_chain_upper
-- name    : OAI.Kadison.FinitePatching.admissible_chain_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:34:01.14408+00:00
-- url     : https://prove2.me/theorems/9bfa38a6-e5d4-4675-ac69-04daa4673c0b
-- title:
--   OAI.Kadison.FinitePatching.admissible_chain_upper: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching`, with `open scoped ComplexOrder Topology`, `open Filter`, `open Words`):
--
--   ```lean
--   lemma admissible_chain_upper (hnormal : NormalGNS.BoundedWOTContinuous M τ)
--       (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
--       (N : ℕ) (ε η : ℝ) (c : Set (PartialUnitary M))
--       (hcs : c ⊆ Admissible M R τ x k N ε η) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
--       ∃ v∈Admissible M R τ x k N ε η,∀ w∈c,w ≤ v
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.FinitePatching.PartialUnitary` (definitions bundle `OAIQ039C009` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.FinitePatching.PartialUnitary.instPartialOrder` (definitions bundle `OAIQ039C046` of this split); `OAI.Kadison.FinitePatching.Admissible` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.exists_almost_full_finite_tests` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C059

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

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

open Words

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {J K : Type*} (x : J → M) (k : K → ℤ)

include hτ in
lemma admissible_chain_upper (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hone : τ 1=1) (hx : ∀ j,‖x j‖ ≤ 1)
    (N : ℕ) (ε η : ℝ) (c : Set (PartialUnitary M))
    (hcs : c ⊆ Admissible M R τ x k N ε η) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
    ∃ v∈Admissible M R τ x k N ε η,∀ w∈c,w ≤ v := by
  sorry

end Kadison.FinitePatching

end

end
end

end OAI
end
