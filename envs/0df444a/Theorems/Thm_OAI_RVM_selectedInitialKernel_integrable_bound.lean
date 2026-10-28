-- Prove2me | Theorems.Thm_OAI_RVM_selectedInitialKernel_integrable_bound
-- name    : OAI.RVM.selectedInitialKernel_integrable_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:29:06.921223+00:00
-- url     : https://prove2.me/theorems/7aff2480-5827-4ea8-a3bf-145bb42f8f0d
-- title:
--   OAI.RVM.selectedInitialKernel_integrable_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.selectedInitialKernel_integrable_bound` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/InitialPuncturedCone.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/InitialPuncturedCone.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open scoped Topology ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma selectedInitialKernel_integrable_bound {f : Phase→ℝ}
--       (hf : Continuous f) (hc : HasCompactSupport f) (hpos : ∀ z,0≤f z) :
--       ∃ C : ℝ,0≤C ∧ ∀ (E B : Field) (T : ℝ) (F : PhaseFlowOn E B T)
--         (zX : Phase) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
--         (W : ℝ→Vec→L[ℝ]Vec) (M : ℝ),
--         0≤T → 0≤M → ContinuousOn ψ (Icc 0 T) → ContinuousOn W (Icc 0 T) →
--         (∀ t∈Icc 0 T,‖W t‖≤M) →
--         Integrable (selectedInitialKernel F.flow zX T f Q ψ W) ∧
--         ‖∫ z : Phase,selectedInitialKernel F.flow zX T f Q ψ W z‖ ≤
--           C*T*M*(∫ t in Ioo (0:ℝ) T,|ψ t|)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.PhaseFlowOn` and `OAI.RVM.selectedInitialKernel` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Field`, `OAI.RVM.Phase` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.direction_physical_family_log_bound`, `OAI.RVM.Admissible.force_bulk_receiver_residual_uniform` and `OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/InitialPuncturedCone.lean (declaration OAI.RVM.selectedInitialKernel_integrable_bound)

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

section
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
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma selectedInitialKernel_integrable_bound {f : Phase→ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hpos : ∀ z,0≤f z) :
    ∃ C : ℝ,0≤C ∧ ∀ (E B : Field) (T : ℝ) (F : PhaseFlowOn E B T)
      (zX : Phase) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
      (W : ℝ→Vec→L[ℝ]Vec) (M : ℝ),
      0≤T → 0≤M → ContinuousOn ψ (Icc 0 T) → ContinuousOn W (Icc 0 T) →
      (∀ t∈Icc 0 T,‖W t‖≤M) →
      Integrable (selectedInitialKernel F.flow zX T f Q ψ W) ∧
      ‖∫ z : Phase,selectedInitialKernel F.flow zX T f Q ψ W z‖ ≤
        C*T*M*(∫ t in Ioo (0:ℝ) T,|ψ t|) := by
  sorry

end RVM

end

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
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

end

end OAI
end
