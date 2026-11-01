-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_PortCSP_witness_energy_le_s53
-- name    : OAI.MetricKMedian.PCP.PortCSP.witness_energy_le_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:40:08.186664+00:00
-- url     : https://prove2.me/theorems/cc3e6037-750f-4410-8a30-977d18f8e0c7
-- title:
--   OAI.MetricKMedian.PCP.PortCSP.witness_energy_le_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.PortCSP.witness_energy_le` of [lean/OAI/Combinatorics/KMedian/Amplification/PoweringMoment.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Amplification/PoweringMoment.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.PortCSP`, with `open Finset`, `open scoped BigOperators`):
--
--   ```lean
--   theorem witness_energy_le_s53 (hG : G.Contracts (1/2)) (a : V → Advice D A cap)
--       (x : V → A) (t L : ℕ) :
--       energy (C.stoppedWitness a x t L) ≤
--         5*cap*testRate (C.Bad x) + (cap:ℝ)^2*(testRate (C.Bad x))^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.Advice` and `OAI.MetricKMedian.PCP.testRate` (definitions bundle `OAIQ053K008` of this split); `OAI.MetricKMedian.PCP.PortGraph` and `OAI.MetricKMedian.PCP.PortGraph.Walk` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.energy` (definitions bundle `OAIQ053K010` of this split); `OAI.MetricKMedian.PCP.PortCSP` and `OAI.MetricKMedian.PCP.PortCSP.Bad` (definitions bundle `OAIQ053K023` of this split); `OAI.MetricKMedian.PCP.PortGraph.Walk.instFintype` (definitions bundle `OAIQ053K025` of this split); `OAI.MetricKMedian.PCP.PortGraph.Contracts` (definitions bundle `OAIQ053K026` of this split); `OAI.MetricKMedian.PCP.PortCSP.stoppedWitness` (definitions bundle `OAIQ053K043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.PCP.PortCSP.powered_sound_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Amplification/PoweringMoment.lean (declaration OAI.MetricKMedian.PCP.PortCSP.witness_energy_le)

import Mathlib
import Definitions.Def_OAIQ053K043

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringMoment

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}

omit [Fintype A] in
theorem witness_energy_le_s53 (hG : G.Contracts (1/2)) (a : V → Advice D A cap)
    (x : V → A) (t L : ℕ) :
    energy (C.stoppedWitness a x t L) ≤
      5*cap*testRate (C.Bad x) + (cap:ℝ)^2*(testRate (C.Bad x))^2 := by
  sorry

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringMoment

end OAI
end
