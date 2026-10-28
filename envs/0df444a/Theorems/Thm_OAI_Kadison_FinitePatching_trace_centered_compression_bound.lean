-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_trace_centered_compression_bound
-- name    : OAI.Kadison.FinitePatching.trace_centered_compression_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:34:11.145545+00:00
-- url     : https://prove2.me/theorems/7d068e4d-4a21-4669-8161-242cd28767d3
-- title:
--   OAI.Kadison.FinitePatching.trace_centered_compression_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching`, with `open scoped ComplexOrder`, `open TracialL2`):
--
--   ```lean
--   lemma trace_centered_compression_bound {p q b a c w z : A}
--       (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q ≤ p)
--       (hw : w*q=w) (hz : q*z=z)
--       (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hwn : ‖w‖ ≤ 1) (hzn : ‖z‖ ≤ 1)
--       {δ : ℝ} (hδ : 0 ≤ δ)
--       (hsmall : norm τ (q*cornerCenter τ p b*q)^2 ≤ δ^2*(τ q).re) :
--       ‖τ (a*w*b*z*c)‖ ≤ (δ+‖cornerScalar τ p b‖)*(τ q).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FinitePatching.cornerCenter` and `OAI.Kadison.FinitePatching.cornerScalar` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialL2.norm` (definitions bundle `OAIQ039C017` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FinitePatching.Words.word_perturbation_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C010
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

open scoped ComplexOrder

namespace Kadison.FinitePatching

open TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma trace_centered_compression_bound {p q b a c w z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q ≤ p)
    (hw : w*q=w) (hz : q*z=z)
    (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hwn : ‖w‖ ≤ 1) (hzn : ‖z‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : norm τ (q*cornerCenter τ p b*q)^2 ≤ δ^2*(τ q).re) :
    ‖τ (a*w*b*z*c)‖ ≤ (δ+‖cornerScalar τ p b‖)*(τ q).re := by
  sorry

end Kadison.FinitePatching

end

end
end

end OAI
end
