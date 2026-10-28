-- Prove2me | Theorems.Thm_OAI_Balanced_ExternalWitnessTail_candidateSlots_of_uniform_moment
-- name    : OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:09:21.708974+00:00
-- url     : https://prove2.me/theorems/f72f3c65-ea38-4340-ad61-d8b34d666b57
-- title:
--   OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment: intermediate lemma from OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Balanced.main_result`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Balanced counterexamples to Ryser's conjecture at prime orders (result family 162)*, OpenAI Math Release, September 27, 2026, result family 162, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment` of [lean/OAI/Combinatorics/BalancedRyser/Candidates/ExternalWitnessTail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Candidates/ExternalWitnessTail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Balanced.ExternalWitnessTail`, with `open scoped Classical BigOperators Topology`, `open MeasureTheory Filter CandidateExposure ExternalAssembly`):
--
--   ```lean
--   theorem candidateSlots_of_uniform_moment (B : ℝ) (hB : 0 ≤ B)
--       (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
--       [∀ n, DecidableEq (K n)]
--       (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
--       (hmoment : ∀ n (g : Direction (K n)),
--         (∫ M, ((witnesses g M).card : ℝ)^400 ∂(offsetLaw (K n)).toMeasure) ≤ B) :
--       Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
--         ∀ s, CandidateAbundanceAssembly.slotLinearConstant * Fintype.card (K n) ≤
--           ((candidateSlot M s).card : ℝ) ∧
--           (candidateSlot M s).card ≤ Fintype.card (K n)}) atTop (𝓝 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Balanced.CandidateVertex`, `OAI.Balanced.Direction`, `OAI.Balanced.MergedPairs`, `OAI.Balanced.Slot`, `OAI.Balanced.candidateSlot`, `OAI.Balanced.offsetEventProbability`, `OAI.Balanced.offsetLaw`, `OAI.Balanced.CandidateAbundanceAssembly.slotLinearConstant`, `OAI.Balanced.ExternalAssembly.WitnessKey` and `OAI.Balanced.ExternalAssembly.witnesses` (definitions bundle `OAIQ63Br000` of this split); `OAI.Balanced.ExternalWitnessTail.instMeasurableSpace_solutions` (definitions bundle `OAIQ63Br001` of this split).
--
--   **Used by.** The proof of `OAI.Balanced.candidateGraph_proof` of this split imports it.
-- source:
--   OpenAI, Balanced counterexamples to Ryser's conjecture at prime orders (result family 162), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 162; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/BalancedRyser/Candidates/ExternalWitnessTail.lean (declaration OAI.Balanced.ExternalWitnessTail.candidateSlots_of_uniform_moment)

import Mathlib
import Definitions.Def_OAIQ63Br000
import Definitions.Def_OAIQ63Br001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ExternalWitnessTail

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Filter CandidateExposure ExternalAssembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

attribute [local instance] OAI.Balanced.ExternalWitnessTail.instMeasurableSpace_solutions
theorem candidateSlots_of_uniform_moment (B : ℝ) (hB : 0 ≤ B)
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
    (hmoment : ∀ n (g : Direction (K n)),
      (∫ M, ((witnesses g M).card : ℝ)^400 ∂(offsetLaw (K n)).toMeasure) ≤ B) :
    Tendsto (fun n => offsetEventProbability {M : MergedPairs (K n) |
      ∀ s, CandidateAbundanceAssembly.slotLinearConstant * Fintype.card (K n) ≤
        ((candidateSlot M s).card : ℝ) ∧
        (candidateSlot M s).card ≤ Fintype.card (K n)}) atTop (𝓝 1) := by
  sorry

end
end Balanced.ExternalWitnessTail

end OAI
end
