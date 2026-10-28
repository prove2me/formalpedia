-- Prove2me | Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_selected_multiplier_decomposition
-- name    : OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:30:15.912892+00:00
-- url     : https://prove2.me/theorems/5e6611a5-d793-43c8-bb01-657426f2e916
-- title:
--   OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceForceConeKernel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceForceConeKernel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma SmoothClassicalPrefix.selected_multiplier_decomposition {d : Datum} {s : Solution} {T : ℝ}
--       (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
--       (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
--       {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
--       (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0)
--       {W W' : ℝ→Vec→L[ℝ]Vec} (hW : Continuous W) (hW' : Continuous W')
--       (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
--       (∫t in Ioo (0:ℝ) T,ψ t • W t
--         (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
--           boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
--         (4*Real.pi)⁻¹ • ((∫p,W (labelReceiverTime F.flow zX T p)
--           (unselectedLabelSignedForce s F.flow zX T Q ψ p))+
--           (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ W z)+
--           ∫p,selectedMultiplierCosts s F.flow zX T Q ψ W W' p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.PhaseFlowOn`, `OAI.RVM.SmoothClassicalPrefix`, `OAI.RVM.boundaryLorentzForce`, `OAI.RVM.datumBoundarySolution`, `OAI.RVM.labelReceiverTime`, `OAI.RVM.selectedInitialKernel` and `OAI.RVM.selectedMultiplierCosts` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.unselectedLabelSignedForce` (definitions bundle `OAIQ073V002` of this split); `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.cross` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.force_bulk_receiver_residual_uniform` and `OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceForceConeKernel.lean (declaration OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V002

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
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma SmoothClassicalPrefix.selected_multiplier_decomposition {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : Continuous W) (hW' : Continuous W')
    (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    (∫t in Ioo (0:ℝ) T,ψ t • W t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
      (4*Real.pi)⁻¹ • ((∫p,W (labelReceiverTime F.flow zX T p)
        (unselectedLabelSignedForce s F.flow zX T Q ψ p))+
        (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ W z)+
        ∫p,selectedMultiplierCosts s F.flow zX T Q ψ W W' p) := by
  sorry

end RVM

end

end OAI
end
