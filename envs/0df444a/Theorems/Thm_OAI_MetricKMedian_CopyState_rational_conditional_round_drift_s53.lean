-- Prove2me | Theorems.Thm_OAI_MetricKMedian_CopyState_rational_conditional_round_drift_s53
-- name    : OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:38:35.277177+00:00
-- url     : https://prove2.me/theorems/5e55ada2-a69c-428c-b579-9579b7f9effe
-- title:
--   OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.CopyState.rational_conditional_round_drift` of [lean/OAI/Combinatorics/KMedian/Sparse/SparseConditionalRoundDrift.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseConditionalRoundDrift.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.CopyState`, with `open Finset PhysicalPotential FixedBatch Analytic`):
--
--   ```lean
--   theorem rational_conditional_round_drift_s53 (A S S₀ : Finset (Copy (F := F) Δ))
--       (G : A → Finset A) (g β p φ : ℚ)
--       (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (enum : Fin n ≃ HeavyAction (RationalBatchData.graph G)
--         (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
--       {x h R : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
--       (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i)
--       (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
--       (hφ1 : (φ:ℝ) ≤ 1)
--       (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
--       (hSA : S ⊆ A) (hS : S ⊆ S₀) (hm₀ : mass g S₀=1)
--       (hd0 : ∀ f, 0 ≤ d f) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, d i.1 ≤ R)
--       (hR : ∃ i ∈ S₀, R=d i.1) :
--       let H := RationalBatchData.heavySet (RationalBatchData.graphMass G g) β
--       let μ := RationalBatchData.proposal G Δ g β p φ hp hφ hupper enum
--       μ.real.expect (fun Z => potential (x*Real.exp (-h)) g (fun i => d i.1)
--         (roundAlive A S G H Z x g d)
--         (GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))))-
--         potential x g (fun i => d i.1) S (GroupCap.cap R d (integral Δ A))) ≤
--       h*(timeRate x (mass g S)*PhysicalPotential.cost g (fun i => d i.1) S+
--         (g:ℝ)*(∑ e ∈ relevant (graphActions G) (localSet A S),
--           charge (graphActions G) x g (GroupCap.cap R d (integral Δ A))
--             (fun i => d i.val.1) (localSet A S) e))+
--         batchConstant Δ*h*((φ:ℝ)+h)*R
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.timeRate` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.CopyState.Copy`, `OAI.MetricKMedian.CopyState.integral` and `OAI.MetricKMedian.CopyState.own` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.FixedBatch.batchConstant` (definitions bundle `OAIQ053K003` of this split); `OAI.MetricKMedian.FiniteLaw.expect`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction`, `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction`, `OAI.MetricKMedian.RationalBatchData.graph`, `OAI.MetricKMedian.RationalBatchData.graphMass` and `OAI.MetricKMedian.RationalBatchData.heavySet` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.GroupCap.cap` and `OAI.MetricKMedian.PhysicalPotential.cost` (definitions bundle `OAIQ053K007` of this split); `OAI.MetricKMedian.CopyState.localSet` and `OAI.MetricKMedian.PhysicalPotential.savingsFraction` (definitions bundle `OAIQ053K015` of this split); `OAI.MetricKMedian.SparseIntegerLaw` and `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ053K016` of this split); `OAI.MetricKMedian.CopyState.next` (definitions bundle `OAIQ053K017` of this split); `OAI.MetricKMedian.CopyState.roundErased`, `OAI.MetricKMedian.CopyState.roundOpened`, `OAI.MetricKMedian.FixedBatch.graphActions` and `OAI.MetricKMedian.FixedBatch.relevant` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.FixedBatch.charge` and `OAI.MetricKMedian.PhysicalPotential.potential` (definitions bundle `OAIQ053K020` of this split); `OAI.MetricKMedian.CopyState.roundAlive` (definitions bundle `OAIQ053K032` of this split); `OAI.MetricKMedian.RationalBatchData.proposal` (definitions bundle `OAIQ053K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseConditionalRoundDrift.lean (declaration OAI.MetricKMedian.CopyState.rational_conditional_round_drift)

import Mathlib
import Definitions.Def_OAIQ053K020
import Definitions.Def_OAIQ053K032
import Definitions.Def_OAIQ053K039

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F : Type} [DecidableEq F] [Fintype F] {Δ n : ℕ}

theorem rational_conditional_round_drift_s53 (A S S₀ : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (g β p φ : ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (enum : Fin n ≃ HeavyAction (RationalBatchData.graph G)
      (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β))
    {x h R : ℝ} (d : F → ℝ) (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hφ1 : (φ:ℝ) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hSA : S ⊆ A) (hS : S ⊆ S₀) (hm₀ : mass g S₀=1)
    (hd0 : ∀ f, 0 ≤ d f) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S₀, d i.1 ≤ R)
    (hR : ∃ i ∈ S₀, R=d i.1) :
    let H := RationalBatchData.heavySet (RationalBatchData.graphMass G g) β
    let μ := RationalBatchData.proposal G Δ g β p φ hp hφ hupper enum
    μ.real.expect (fun Z => potential (x*Real.exp (-h)) g (fun i => d i.1)
      (roundAlive A S G H Z x g d)
      (GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z))))-
      potential x g (fun i => d i.1) S (GroupCap.cap R d (integral Δ A))) ≤
    h*(timeRate x (mass g S)*PhysicalPotential.cost g (fun i => d i.1) S+
      (g:ℝ)*(∑ e ∈ relevant (graphActions G) (localSet A S),
        charge (graphActions G) x g (GroupCap.cap R d (integral Δ A))
          (fun i => d i.val.1) (localSet A S) e))+
      batchConstant Δ*h*((φ:ℝ)+h)*R := by
  sorry

end MetricKMedian.CopyState
end
end

end OAI
end
