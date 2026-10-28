-- Prove2me | Theorems.Thm_OAI_Kadison_RelativeCornerQuantization_exists_polar_cut
-- name    : OAI.Kadison.RelativeCornerQuantization.exists_polar_cut
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:47:52.211043+00:00
-- url     : https://prove2.me/theorems/90a12c1b-ba22-44a2-ab6e-728daa637a88
-- title:
--   OAI.Kadison.RelativeCornerQuantization.exists_polar_cut: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.RelativeCornerQuantization`, with `open scoped ComplexOrder InnerProductSpace Topology BigOperators`, `open Filter`, `open TracialL2`):
--
--   ```lean
--   theorem exists_polar_cut (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q)
--       {c t : ℝ} (hc : 0 ≤ c) (hct : c*c*t=1) :
--       ∃ f : M, IsStarProjection f ∧ f ≤ p ∧ (τ f).re ≤ (τ q).re ∧
--         (τ q).re-(τ f).re ≤ (c^2*norm τ (q*(p-t • (1:M))*q))^2 ∧
--         (∀ y : M, p*y=y → y*p=y → norm τ (f*y*f) ≤
--           c^2*norm τ (q*y*q)+(1+c)*‖y‖*c^2*norm τ (q*(p-t • (1:M))*q)) ∧
--         (∀ N : VonNeumannAlgebra H, (p : H →L[ℂ] H)∈N → (q : H →L[ℂ] H)∈N →
--           (f : H →L[ℂ] H)∈N)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.TracialL2.norm` (definitions bundle `OAIQ039C017` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.RelativeCornerQuantization.exists_relative_centered_compression` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C017
import Definitions.Def_OAIQ039C022

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

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.RelativeCornerQuantization

open TracialL2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ in
theorem exists_polar_cut (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q)
    {c t : ℝ} (hc : 0 ≤ c) (hct : c*c*t=1) :
    ∃ f : M, IsStarProjection f ∧ f ≤ p ∧ (τ f).re ≤ (τ q).re ∧
      (τ q).re-(τ f).re ≤ (c^2*norm τ (q*(p-t • (1:M))*q))^2 ∧
      (∀ y : M, p*y=y → y*p=y → norm τ (f*y*f) ≤
        c^2*norm τ (q*y*q)+(1+c)*‖y‖*c^2*norm τ (q*(p-t • (1:M))*q)) ∧
      (∀ N : VonNeumannAlgebra H, (p : H →L[ℂ] H)∈N → (q : H →L[ℂ] H)∈N →
        (f : H →L[ℂ] H)∈N) := by
  sorry

end Kadison.RelativeCornerQuantization

end

end
end

end OAI
end
