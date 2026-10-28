-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_labelConeKernel_triangle_weighted_norm
-- name    : OAI.RVM.PhaseFlowOn.labelConeKernel_triangle_weighted_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:18:16.638246+00:00
-- url     : https://prove2.me/theorems/82a93206-b1f8-42bd-91d5-b8801853ae33
-- title:
--   OAI.RVM.PhaseFlowOn.labelConeKernel_triangle_weighted_norm: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.labelConeKernel_triangle_weighted_norm` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/ArrivalConeKernelPolarNorm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ArrivalConeKernelPolarNorm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.labelConeKernel_triangle_weighted_norm {s : Solution} {T : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
--       {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T))
--       {b : ℝ→ℝ} (hb : Measurable b) :
--       (∫⁻p : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T p))*ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
--         ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
--           ENNReal.ofReal (b t)*ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
--           ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
--             A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ ∂volume ∂sphereMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ConeKernelState`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.coneKernelDomain`, `OAI.RVM.labelConeKernel`, `OAI.RVM.labelReceiverTime` and `OAI.RVM.sphereMeasure` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.dot` and `OAI.RVM.velocity` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.label_moving_primitive_near_constant` and `OAI.RVM.Admissible.label_projected_primitive_near_constant` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/ArrivalConeKernelPolarNorm.lean (declaration OAI.RVM.PhaseFlowOn.labelConeKernel_triangle_weighted_norm)

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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.labelConeKernel_triangle_weighted_norm {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T))
    {b : ℝ→ℝ} (hb : Measurable b) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T p))*ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (b t)*ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ ∂volume ∂sphereMeasure := by
  sorry

end RVM

end

end OAI
end
