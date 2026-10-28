-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_cone_occupation_angular_bound
-- name    : OAI.RVM.PhaseFlowOn.cone_occupation_angular_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:17:51.305468+00:00
-- url     : https://prove2.me/theorems/66b84bb8-3a20-4b02-ab3f-acafc1388a88
-- title:
--   OAI.RVM.PhaseFlowOn.cone_occupation_angular_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.cone_occupation_angular_bound` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/SpaceConeDomain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SpaceConeDomain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma PhaseFlowOn.cone_occupation_angular_bound {E B : Field} {T δ Δ a b : ℝ}
--       (F : PhaseFlowOn E B T) (hT : 0 ≤ T) (zX : Phase) {f : Particle}
--       (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase))) (heq : VlasovOn f E B T)
--       {H : Set (ℝ × Phase)} (hH : MeasurableSet H)
--       (hsub : H ⊆ spaceConeDomain F.flow zX T) (hδ : 0 ≤ δ) (hΔ : 0 < Δ)
--       (hsource : ∀ z s, (s,z) ∈ phaseHits F.flow T H →
--         δ ≤ 1-dot (branchDirection F.flow zX z T s) (velocity (F.flow z s).2))
--       (hreceiver : ∀ z s, (s,z) ∈ phaseHits F.flow T H →
--         1-dot (branchDirection F.flow zX z T s)
--           (velocity (F.flow zX (branchTime F.flow zX z T s)).2) ≤ Δ)
--       (himage : ∀ z, branchTime F.flow zX z T '' {s | (s,z) ∈ phaseHits F.flow T H} ⊆ Icc a b) :
--       ENNReal.ofReal (δ/Δ) * coneOccupation F.flow zX T f H ≤
--         ENNReal.ofReal (b-a) * ∫⁻ z, ENNReal.ofReal (f (0,z))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.PhaseFlowOn`, `OAI.RVM.VlasovOn`, `OAI.RVM.branchDirection`, `OAI.RVM.branchTime`, `OAI.RVM.coneOccupation`, `OAI.RVM.phaseHits` and `OAI.RVM.spaceConeDomain` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Field`, `OAI.RVM.Particle`, `OAI.RVM.Phase`, `OAI.RVM.Vec`, `OAI.RVM.dot` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direct_source_large_radius`, `OAI.RVM.Admissible.representative_magnetic_large` and `OAI.RVM.Admissible.source_majorant_large_radius` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SpaceConeDomain.lean (declaration OAI.RVM.PhaseFlowOn.cone_occupation_angular_bound)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.cone_occupation_angular_bound {E B : Field} {T δ Δ a b : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0 ≤ T) (zX : Phase) {f : Particle}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase))) (heq : VlasovOn f E B T)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H)
    (hsub : H ⊆ spaceConeDomain F.flow zX T) (hδ : 0 ≤ δ) (hΔ : 0 < Δ)
    (hsource : ∀ z s, (s,z) ∈ phaseHits F.flow T H →
      δ ≤ 1-dot (branchDirection F.flow zX z T s) (velocity (F.flow z s).2))
    (hreceiver : ∀ z s, (s,z) ∈ phaseHits F.flow T H →
      1-dot (branchDirection F.flow zX z T s)
        (velocity (F.flow zX (branchTime F.flow zX z T s)).2) ≤ Δ)
    (himage : ∀ z, branchTime F.flow zX z T '' {s | (s,z) ∈ phaseHits F.flow T H} ⊆ Icc a b) :
    ENNReal.ofReal (δ/Δ) * coneOccupation F.flow zX T f H ≤
      ENNReal.ofReal (b-a) * ∫⁻ z, ENNReal.ofReal (f (0,z)) := by
  sorry

end RVM

end

end OAI
end
