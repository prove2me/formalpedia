-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCompletionFair_result_guarantee_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:02.787495+00:00
-- url     : https://prove2.me/theorems/ed4357a4-1bc3-4c0d-ab86-1ae6ca4a1a8a
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/CompletionResultGuarantee.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/CompletionResultGuarantee.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair`, with `open Completion Categorical FiniteSampling`):
--
--   ```lean
--   lemma result_guarantee_s238r
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
--       (hp : Function.Surjective part) (hw : ∀ i,0≤weight i) :
--       (∀ bits, result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits ⊆ F ∧
--         (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).card=S.card ∧
--         (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).Nonempty) ∧
--       ∀ X, PartitionFeasible part X →
--         average (fun bits=> realCost D (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits)) ≤
--         (38/100:ℝ)*surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
--           (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) ∅ +
--         (62/100:ℝ)*surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
--           (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) X
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.Completion.surrogate`, `OAI.MetricKMedianRecovery.FiniteSampling.average`, `OAI.MetricKMedianRecovery.SortedIndex.enum`, `OAI.MetricKMedianRecovery.Categorical.Explicit.exponent` and `OAI.MetricKMedianRecovery.Categorical.Explicit.samples` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Categorical.PartitionFeasible`, `OAI.MetricKMedianRecovery.Completion.Virtual`, `OAI.MetricKMedianRecovery.Completion.assignmentWeight`, `OAI.MetricKMedianRecovery.Completion.realCost`, `OAI.MetricKMedianRecovery.Completion.virtualDistance`, `OAI.MetricKMedianRecovery.Completion.virtualNearest` and `OAI.MetricKMedianRecovery.Completion.withGhosts` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq` and `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype` (definitions bundle `Q238L010` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/CompletionResultGuarantee.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee)

import Mathlib
import Definitions.Def_Q238L008
import Definitions.Def_Q238L010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFair
open Completion Categorical FiniteSampling
variable {n q a r b : ℕ} [PseudoMetricSpace (Fin n)]
lemma result_guarantee_s238r
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
    (hp : Function.Surjective part) (hw : ∀ i,0≤weight i) :
    (∀ bits, result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits ⊆ F ∧
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).card=S.card ∧
      (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits).Nonempty) ∧
    ∀ X, PartitionFeasible part X →
      average (fun bits=> realCost D (result F S Q part hp o loc redLoc blueLoc blueDest k base distance weight redBase redDistance bits)) ≤
      (38/100:ℝ)*surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) ∅ +
      (62/100:ℝ)*surrogate K k (fun i=>(base i:ℝ)) (fun i e=>(distance i e:ℝ))
        (fun i=>(weight i:ℝ)) (fun i=>(redBase i:ℝ)) (fun i e=>(redDistance i e:ℝ)) X := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCompletionFair

end OAI
end
