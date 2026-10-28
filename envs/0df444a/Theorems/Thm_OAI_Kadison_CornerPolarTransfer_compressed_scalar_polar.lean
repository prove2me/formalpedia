-- Prove2me | Theorems.Thm_OAI_Kadison_CornerPolarTransfer_compressed_scalar_polar
-- name    : OAI.Kadison.CornerPolarTransfer.compressed_scalar_polar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:33:23.597712+00:00
-- url     : https://prove2.me/theorems/ddd866b9-af73-4bc9-aee5-2eb885311965
-- title:
--   OAI.Kadison.CornerPolarTransfer.compressed_scalar_polar: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CornerPolarTransfer`, with `open scoped ComplexOrder InnerProductSpace`, `open TracialL2`):
--
--   ```lean
--   lemma compressed_scalar_polar {p q v b y : A} {c : ℝ}
--       (hp : IsStarProjection p) (hq : IsStarProjection q) (hpy : p*y=y) (hyp : y*p=y)
--       (hb : b=c • (p*q)) (hv : ‖v‖≤1) :
--       norm τ ((v*star v)*y*(v*star v)) ≤ c^2*norm τ (q*y*q)+
--         (1+‖b‖)*‖y‖*norm τ (v-b)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.TracialL2.norm` (definitions bundle `OAIQ039C017` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.RelativeCornerQuantization.exists_polar_cut` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.CornerPolarTransfer

open TracialL2

section Estimates

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma compressed_scalar_polar {p q v b y : A} {c : ℝ}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpy : p*y=y) (hyp : y*p=y)
    (hb : b=c • (p*q)) (hv : ‖v‖≤1) :
    norm τ ((v*star v)*y*(v*star v)) ≤ c^2*norm τ (q*y*q)+
      (1+‖b‖)*‖y‖*norm τ (v-b) := by
  sorry

end Estimates

end Kadison.CornerPolarTransfer

end

end
end

end OAI
end
