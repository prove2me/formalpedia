-- Prove2me | Theorems.Thm_OAI_Kadison_CornerPolarTransfer_defect_bound
-- name    : OAI.Kadison.CornerPolarTransfer.defect_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:33:34.016969+00:00
-- url     : https://prove2.me/theorems/ff121e4a-9e1b-4e27-a205-31a0cdbdb76a
-- title:
--   OAI.Kadison.CornerPolarTransfer.defect_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CornerPolarTransfer`, with `open scoped ComplexOrder InnerProductSpace`, `open TracialL2`):
--
--   ```lean
--   lemma defect_bound {q r a v : A} (hq : IsStarProjection q)
--       (hr : IsStarProjection r) (hrq : r≤q) (ha : 0≤a)
--       (hra : r*a=a) (haq : a*q=a) (hv : star v*v=r) :
--       norm τ (v-v*a) ≤ norm τ (q-a*a)
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

lemma defect_bound {q r a v : A} (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hrq : r≤q) (ha : 0≤a)
    (hra : r*a=a) (haq : a*q=a) (hv : star v*v=r) :
    norm τ (v-v*a) ≤ norm τ (q-a*a) := by
  sorry

end Estimates

end Kadison.CornerPolarTransfer

end

end
end

end OAI
end
