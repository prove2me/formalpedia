-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_nextTable_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:02:42.597429+00:00
-- url     : https://prove2.me/theorems/f3f8925b-3bea-40a3-8200-6b57aba51a4c
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalChoice.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalChoice.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma nextTable_pack_s238r (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
--       (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
--       (part : Fin q→Fin a) (hp : Function.Surjective part) (s : Categorical.GreedyState (Fin q) a T)
--       (ht : s.1<T) (seed : Categorical.OracleSeed (Fin q) a T L) :
--       nextTable g (pairBits (stepContext ctx part T,pairBits (oracleBits seed,stateBits s)))=
--         tableBits elemBits (Categorical.advance s.2 ⟨s.1,ht⟩
--           ((rule part hp).choose (Categorical.scores part (fun S=>(G S:ℝ)) s.2 seed)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238L001` of this split); `OAI.MetricKMedianRecovery.Categorical.GreedyState`, `OAI.MetricKMedianRecovery.Categorical.OracleSeed`, `OAI.MetricKMedianRecovery.Categorical.Table`, `OAI.MetricKMedianRecovery.Categorical.advance`, `OAI.MetricKMedianRecovery.Categorical.scores` and `OAI.MetricKMedianRecovery.Categorical.Selected.Rule` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elemBits` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238L006` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.rule` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.oracleBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.stateBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.stepContext` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.tableBits` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable` (definitions bundle `Q238L037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalChoice.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q a T L : ℕ}
attribute [local irreducible] advance choices
lemma nextTable_pack_s238r (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (hp : Function.Surjective part) (s : Categorical.GreedyState (Fin q) a T)
    (ht : s.1<T) (seed : Categorical.OracleSeed (Fin q) a T L) :
    nextTable g (pairBits (stepContext ctx part T,pairBits (oracleBits seed,stateBits s)))=
      tableBits elemBits (Categorical.advance s.2 ⟨s.1,ht⟩
        ((rule part hp).choose (Categorical.scores part (fun S=>(G S:ℝ)) s.2 seed))) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end
