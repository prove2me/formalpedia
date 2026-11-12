-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_favorable_literal_plan_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:32:42.71586+00:00
-- url     : https://prove2.me/theorems/21573b67-4522-4149-a11d-270009922c64
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchObjective.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchObjective.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram`, with `open Completion Categorical FiniteSampling BinaryBranchContext Sampling`):
--
--   ```lean
--   lemma favorable_literal_plan_s238r [Nonempty (Fin n)]
--       (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
--       (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty) (hOF : O⊆F)
--       (Δ : ℚ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
--       (hcolors : ∀ u∈(C.nonproxy\s.real.deleted)∪designatedProxies (C.nonproxy\s.real.deleted)
--         (C.designatedDestination hD s.real (19/50)),colors u=requiredColors (C.nonproxy\s.real.deleted)
--         (C.designatedDestination hD s.real (19/50)) u)
--       (label : Fin n→Fin m)
--       (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
--       (hinj : Set.InjOn label (↑(designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)))))
--       (r0 y0 : Fin n) :
--       let blue:=(S\s.deleted).filter (fun i=>colors i=2)
--       let score:=rationalScore δ D S Δ s
--       let bd:=designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))
--       let c:=(bd.image (C.blueDestination hD s.real (19/50))).card
--       ∃ v xs,∃ h : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs),
--         let P:=BlueDP.makePlan blue F label score c r0 y0 v xs h
--         (∑ l,branchScore D S (Δ:ℝ) s.real (P.sel l) (P.dst l))≤
--           ∑ u∈bd,assignmentWeight D (completionAssignment S (Δ:ℝ) s.real) u*
--             minimumMixed (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
--               (C.destinations s.real) (C.destinations_nonempty hD s.real) u
--   ```
--
--   **Definitions.** The statement is written with `OAI.BlueSubsetDP.Plan` (definitions bundle `Q238L000` of this split); `OAI.MetricKMedianRecovery.BlueDP.Atom`, `OAI.MetricKMedianRecovery.BlueDP.Candidate`, `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rationalScore`, `OAI.MetricKMedianRecovery.RationalSampling.State.real` and `OAI.MetricKMedianRecovery.Sampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Completion.assignmentWeight`, `OAI.MetricKMedianRecovery.Completion.designatedBlue`, `OAI.MetricKMedianRecovery.Completion.designatedProxies`, `OAI.MetricKMedianRecovery.Completion.minimumMixed`, `OAI.MetricKMedianRecovery.Completion.requiredColors` and `OAI.MetricKMedianRecovery.Sampling.Comparison` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BlueDP.best` and `OAI.MetricKMedianRecovery.BlueDP.block` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.Sampling.completionAssignment`, `OAI.MetricKMedianRecovery.Sampling.leafCenter`, `OAI.MetricKMedianRecovery.Sampling.leafRadius`, `OAI.MetricKMedianRecovery.Sampling.Comparison.blueDestination`, `OAI.MetricKMedianRecovery.Sampling.Comparison.coveredCenter`, `OAI.MetricKMedianRecovery.Sampling.Comparison.designatedDestination`, `OAI.MetricKMedianRecovery.Sampling.Comparison.destinations`, `OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_nonempty` and `OAI.MetricKMedianRecovery.Sampling.Comparison.nonproxy` (definitions bundle `Q238L011` of this split); `OAI.MetricKMedianRecovery.BlueDP.makePlan` (definitions bundle `Q238L018` of this split); `OAI.MetricKMedianRecovery.Sampling.branchScore` (definitions bundle `Q238L021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.successful_probability_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchObjective.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan)

import Mathlib
import Definitions.Def_Q238L018
import Definitions.Def_Q238L021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext Sampling
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
lemma favorable_literal_plan_s238r [Nonempty (Fin n)]
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty) (hOF : O⊆F)
    (Δ : ℚ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (hcolors : ∀ u∈(C.nonproxy\s.real.deleted)∪designatedProxies (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)),colors u=requiredColors (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)) u)
    (label : Fin n→Fin m)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
    (hinj : Set.InjOn label (↑(designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)))))
    (r0 y0 : Fin n) :
    let blue:=(S\s.deleted).filter (fun i=>colors i=2)
    let score:=rationalScore δ D S Δ s
    let bd:=designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))
    let c:=(bd.image (C.blueDestination hD s.real (19/50))).card
    ∃ v xs,∃ h : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs),
      let P:=BlueDP.makePlan blue F label score c r0 y0 v xs h
      (∑ l,branchScore D S (Δ:ℝ) s.real (P.sel l) (P.dst l))≤
        ∑ u∈bd,assignmentWeight D (completionAssignment S (Δ:ℝ) s.real) u*
          minimumMixed (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
            (C.destinations s.real) (C.destinations_nonempty hD s.real) u := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end
