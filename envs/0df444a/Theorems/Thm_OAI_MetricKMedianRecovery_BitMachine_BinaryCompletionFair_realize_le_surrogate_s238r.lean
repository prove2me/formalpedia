-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCompletionFair_realize_le_surrogate_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:22:16.32322+00:00
-- url     : https://prove2.me/theorems/aa010075-f5cc-4db2-b51e-941ddad59bde
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CompletionFairCorrect.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CompletionFairCorrect.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair`, with `open Completion`):
--
--   ```lean
--   lemma realize_le_surrogate_s238r
--       (D F S Q G : Finset (Fin n)) (hS : S⊆F) (hn : S.Nonempty) (hQ : Q⊆S)
--       (part : Fin q→Fin a) (o : Fin a→Fin q) (ho : ∀ j,part (o j)=j) (loc : Fin q→Fin n)
--       (w : Fin a→Fin n) (radius : Fin a→ℝ) (M : ℝ)
--       (assignment : Fin n→Virtual (Fin n) a)
--       (hamem : ∀ p,assignment p∈withGhosts (S\Q))
--       (hadist : ∀ p,virtualDistance w radius M p (assignment p)=virtualNearest (S\Q) w radius M p)
--       (hr : ∀ i,0 ≤ radius i) (hM0 : 0≤M)
--       (hloc : ∀ e,loc e∈F) (hball : ∀ e,dist (w (part e)) (loc e) ≤ radius (part e))
--       (hM : ∀ x,∀ f∈F,dist x f≤M)
--       (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n)
--       (hredInj : Function.Injective redLoc) (hblueInj : Function.Injective blueLoc)
--       (hred : ∀ i,redLoc i∈S\Q) (hblue : ∀ i,blueLoc i∈S\Q)
--       (hRB : ∀ i j,redLoc i≠blueLoc j)
--       (hG : G⊆S\Q) (hGR : ∀ i,redLoc i∉G) (hGB : ∀ i,blueLoc i∉G)
--       (hdest : ∀ i,blueDest i∈F) (c k : ℕ) (hdestCount : (Finset.univ.image blueDest).card ≤ c)
--       (hcount : a+c≤Q.card+k+b) (hk : k ≤ r) (K : ℝ)
--       (hK : (∑ i,assignmentWeight D assignment (blueLoc i)*dist (blueLoc i) (blueDest i))≤K)
--       (base : Fin D.card→ℚ) (distance : Fin D.card→Fin q→ℚ)
--       (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
--       (hbase : ∀ i,(base i:ℝ)=virtualNearest (S\Q) w radius M (SortedIndex.enum D i))
--       (hdistance : ∀ i e,(distance i e:ℝ)=dist (SortedIndex.enum D i) (loc e))
--       (hweight : ∀ i,(weight i:ℝ)=assignmentWeight D assignment (redLoc i))
--       (hredBase : ∀ i,(redBase i:ℝ)=virtualNearest G w radius M (redLoc i))
--       (hredDistance : ∀ i e,(redDistance i e:ℝ)=dist (redLoc i) (loc e))
--       (xs : List (Fin q)) (hX : Categorical.PartitionFeasible part xs.toFinset) :
--       let T:=BinaryRationalSort.indexSet (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k
--       let U:=Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs T
--       U⊆F ∧ U.card=S.card ∧ ∃ hU:U.Nonempty,
--         (∑ p∈D,distanceTo U hU p)≤
--           surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
--             (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) xs.toFinset
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Completion.surrogate`, `OAI.MetricKMedianRecovery.SortedIndex.enum`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.capped`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.indexSet` and `OAI.MetricKMedianRecovery.Completion.Canonical.realize` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Categorical.PartitionFeasible`, `OAI.MetricKMedianRecovery.Completion.Virtual`, `OAI.MetricKMedianRecovery.Completion.assignmentWeight`, `OAI.MetricKMedianRecovery.Completion.distanceTo`, `OAI.MetricKMedianRecovery.Completion.virtualDistance`, `OAI.MetricKMedianRecovery.Completion.virtualNearest` and `OAI.MetricKMedianRecovery.Completion.withGhosts` (definitions bundle `Q238L004` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CompletionFairCorrect.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.realize_le_surrogate)

import Mathlib
import Definitions.Def_Q238L002
import Definitions.Def_Q238L004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open Completion
variable {n q a r b : ℕ} [PseudoMetricSpace (Fin n)]
lemma realize_le_surrogate_s238r
    (D F S Q G : Finset (Fin n)) (hS : S⊆F) (hn : S.Nonempty) (hQ : Q⊆S)
    (part : Fin q→Fin a) (o : Fin a→Fin q) (ho : ∀ j,part (o j)=j) (loc : Fin q→Fin n)
    (w : Fin a→Fin n) (radius : Fin a→ℝ) (M : ℝ)
    (assignment : Fin n→Virtual (Fin n) a)
    (hamem : ∀ p,assignment p∈withGhosts (S\Q))
    (hadist : ∀ p,virtualDistance w radius M p (assignment p)=virtualNearest (S\Q) w radius M p)
    (hr : ∀ i,0 ≤ radius i) (hM0 : 0≤M)
    (hloc : ∀ e,loc e∈F) (hball : ∀ e,dist (w (part e)) (loc e) ≤ radius (part e))
    (hM : ∀ x,∀ f∈F,dist x f≤M)
    (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n)
    (hredInj : Function.Injective redLoc) (hblueInj : Function.Injective blueLoc)
    (hred : ∀ i,redLoc i∈S\Q) (hblue : ∀ i,blueLoc i∈S\Q)
    (hRB : ∀ i j,redLoc i≠blueLoc j)
    (hG : G⊆S\Q) (hGR : ∀ i,redLoc i∉G) (hGB : ∀ i,blueLoc i∉G)
    (hdest : ∀ i,blueDest i∈F) (c k : ℕ) (hdestCount : (Finset.univ.image blueDest).card ≤ c)
    (hcount : a+c≤Q.card+k+b) (hk : k ≤ r) (K : ℝ)
    (hK : (∑ i,assignmentWeight D assignment (blueLoc i)*dist (blueLoc i) (blueDest i))≤K)
    (base : Fin D.card→ℚ) (distance : Fin D.card→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ)
    (hbase : ∀ i,(base i:ℝ)=virtualNearest (S\Q) w radius M (SortedIndex.enum D i))
    (hdistance : ∀ i e,(distance i e:ℝ)=dist (SortedIndex.enum D i) (loc e))
    (hweight : ∀ i,(weight i:ℝ)=assignmentWeight D assignment (redLoc i))
    (hredBase : ∀ i,(redBase i:ℝ)=virtualNearest G w radius M (redLoc i))
    (hredDistance : ∀ i e,(redDistance i e:ℝ)=dist (redLoc i) (loc e))
    (xs : List (Fin q)) (hX : Categorical.PartitionFeasible part xs.toFinset) :
    let T:=BinaryRationalSort.indexSet (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset) k
    let U:=Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs T
    U⊆F ∧ U.card=S.card ∧ ∃ hU:U.Nonempty,
      (∑ p∈D,distanceTo U hU p)≤
        surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
          (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) xs.toFinset := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

end OAI
end
