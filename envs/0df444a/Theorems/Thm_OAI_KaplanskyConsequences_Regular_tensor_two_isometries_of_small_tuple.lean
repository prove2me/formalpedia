-- Prove2me | Theorems.Thm_OAI_KaplanskyConsequences_Regular_tensor_two_isometries_of_small_tuple
-- name    : OAI.KaplanskyConsequences.Regular.tensor_two_isometries_of_small_tuple
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T15:25:24.960237+00:00
-- url     : https://prove2.me/theorems/b5d36e79-8b74-4d52-9b82-2e1fbe7936d2
-- title:
--   OAI.KaplanskyConsequences.Regular.tensor_two_isometries_of_small_tuple (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KaplanskyConsequences.Regular.tensor_two_isometries_of_small_tuple` of [lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/ReducedTensor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/ReducedTensor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KaplanskyConsequences.Regular`, with `open scoped ComplexOrder InnerProductSpace BigOperators ENNReal`):
--
--   ```lean
--   lemma tensor_two_isometries_of_small_tuple (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
--       {ι : Type*} [Fintype ι] (a : ι → A)
--       (hc : ∑ i, star (a i)*a i = 1)
--       (hr : ∑ i, a i*star (a i) ≤ (1/10000:ℝ) • (1:A)) :
--       ∃ s t : tensorAlgebra (G:=F2) ρ, star s*s=1 ∧ star t*t=1 ∧ star s*t=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.KaplanskyConsequences.Regular.F2`, `OAI.KaplanskyConsequences.Regular.HilbertSum` and `OAI.KaplanskyConsequences.Regular.tensorAlgebra` (the published bundle `Def_KaplanskyStableFiniteness`).
--
--   **Used by.** The proofs of `OAI.KaplanskyConsequences.actualAlgebra_tensor_properlyInfinite` and `OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists` of this split import it.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Regular/ReducedTensor.lean (declaration OAI.KaplanskyConsequences.Regular.tensor_two_isometries_of_small_tuple)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensor_two_isometries_of_small_tuple (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {ι : Type*} [Fintype ι] (a : ι → A)
    (hc : ∑ i, star (a i)*a i = 1)
    (hr : ∑ i, a i*star (a i) ≤ (1/10000:ℝ) • (1:A)) :
    ∃ s t : tensorAlgebra (G:=F2) ρ, star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  sorry

end KaplanskyConsequences.Regular

end

end OAI
end
