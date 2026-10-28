-- Prove2me | Theorems.Thm_OAI_Kadison_IntertwinerCompression_seminorm_le
-- name    : OAI.Kadison.IntertwinerCompression.seminorm_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:43:50.869977+00:00
-- url     : https://prove2.me/theorems/8efa238d-4e55-493e-98b4-d342c590eae6
-- title:
--   OAI.Kadison.IntertwinerCompression.seminorm_le: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.IntertwinerCompression`, with `open scoped InnerProductSpace ComplexOrder`, `open ContinuousLinearMap`):
--
--   ```lean
--   lemma seminorm_le (M : VonNeumannAlgebra H) (Q : VonNeumannAlgebra G)
--       (ψ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (hinj : Function.Injective ψ)
--       (hrange : ∀ b∈Q,∃ a : M,ψ a=b)
--       (T : H →L[ℂ] G) (hcon : ‖T‖≤1)
--       (hT : ∀ a : M,T.comp (a:H →L[ℂ] H)=(ψ a).comp T) (Y : H →L[ℂ] H) :
--       commutatorSeminorm Q (transfer T Y) ≤ commutatorSeminorm M Y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.IntertwinerCompression.transfer` (definitions bundle `OAIQ039C012` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.commutatorSeminorm` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proof of `OAI.Kadison.NormalRepresentation.finite_standard_compression_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C012
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.IntertwinerCompression

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma seminorm_le (M : VonNeumannAlgebra H) (Q : VonNeumannAlgebra G)
    (ψ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (hinj : Function.Injective ψ)
    (hrange : ∀ b∈Q,∃ a : M,ψ a=b)
    (T : H →L[ℂ] G) (hcon : ‖T‖≤1)
    (hT : ∀ a : M,T.comp (a:H →L[ℂ] H)=(ψ a).comp T) (Y : H →L[ℂ] H) :
    commutatorSeminorm Q (transfer T Y) ≤ commutatorSeminorm M Y := by
  sorry

end Kadison.IntertwinerCompression

end

end
end

end OAI
end
