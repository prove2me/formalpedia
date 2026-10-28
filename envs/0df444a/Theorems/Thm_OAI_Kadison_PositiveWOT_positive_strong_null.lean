-- Prove2me | Theorems.Thm_OAI_Kadison_PositiveWOT_positive_strong_null
-- name    : OAI.Kadison.PositiveWOT.positive_strong_null
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:47:34.853024+00:00
-- url     : https://prove2.me/theorems/840dbfbc-36f2-4cae-94a3-6a5ae08f9397
-- title:
--   OAI.Kadison.PositiveWOT.positive_strong_null: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PositiveWOT`, with `open Filter`, `open scoped ComplexOrder InnerProductSpace Topology`):
--
--   ```lean
--   theorem positive_strong_null [TopologicalSpace.SeparableSpace H]
--       (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f)
--       (A : ℕ → M) (hA : ∀ n,0≤A n) (h1 : ∀ n,A n≤1)
--       (ht : ∀ x,Tendsto (fun n => (A n : H →L[ℂ] H) x) atTop (𝓝 0)) :
--       Tendsto (fun n => f (A n)) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.PositiveWOT.ProjectionContinuousAtOne` (definitions bundle `OAIQ039C029` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.PositiveWOT.mem_predual` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C029

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positive_strong_null [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f)
    (A : ℕ → M) (hA : ∀ n,0≤A n) (h1 : ∀ n,A n≤1)
    (ht : ∀ x,Tendsto (fun n => (A n : H →L[ℂ] H) x) atTop (𝓝 0)) :
    Tendsto (fun n => f (A n)) atTop (𝓝 0) := by
  sorry

end Kadison.PositiveWOT

end

end
end

end OAI
end
