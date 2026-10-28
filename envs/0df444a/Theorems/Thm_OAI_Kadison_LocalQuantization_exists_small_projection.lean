-- Prove2me | Theorems.Thm_OAI_Kadison_LocalQuantization_exists_small_projection
-- name    : OAI.Kadison.LocalQuantization.exists_small_projection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:36:03.747491+00:00
-- url     : https://prove2.me/theorems/dc583c01-421f-456d-bf62-c44dd53da020
-- title:
--   OAI.Kadison.LocalQuantization.exists_small_projection: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.LocalQuantization`, with `open scoped InnerProductSpace ComplexOrder Topology BigOperators`, `open Filter`, `open TracialGNS`):
--
--   ```lean
--   theorem exists_small_projection
--       (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
--       (x : J → A)
--       (hx : ∀ j, Tendsto (fun n => algebraVector τ (MatrixExpectation.expectation (stage n) (x j)))
--         atTop (𝓝 0))
--       {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
--       ∃ (n : ℕ) (q : A), q∈(stage n).range ∧ IsStarProjection q ∧
--         0<(τ q).re ∧ (τ q).re<η ∧
--         (∑ j, ‖algebraVector τ (q*x j*q)‖^2)<ε^2*(τ q).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialGNS.algebraVector` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.MatrixExpectation.expectation` (definitions bundle `OAIQ039C012` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.LocalQuantization.exists_centered_compression` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology BigOperators

open Filter

namespace Kadison.LocalQuantization

open TracialGNS

section FiniteTests

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype J]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (hone : τ 1=1)

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, LinearOrder (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] A)

include hτ hone in
theorem exists_small_projection
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (x : J → A)
    (hx : ∀ j, Tendsto (fun n => algebraVector τ (MatrixExpectation.expectation (stage n) (x j)))
      atTop (𝓝 0))
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ (n : ℕ) (q : A), q∈(stage n).range ∧ IsStarProjection q ∧
      0<(τ q).re ∧ (τ q).re<η ∧
      (∑ j, ‖algebraVector τ (q*x j*q)‖^2)<ε^2*(τ q).re := by
  sorry

end FiniteTests

end Kadison.LocalQuantization

end

end
end

end OAI
end
