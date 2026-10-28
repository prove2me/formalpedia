-- Prove2me | Theorems.Thm_OAI_RVM_PhaseFlowOn_physicalBin_magneticField
-- name    : OAI.RVM.PhaseFlowOn.physicalBin_magneticField
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:19:09.385971+00:00
-- url     : https://prove2.me/theorems/2ec50ed8-eedb-41f6-bd3e-41059d0b246b
-- title:
--   OAI.RVM.PhaseFlowOn.physicalBin_magneticField: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.PhaseFlowOn.physicalBin_magneticField` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalProjectedRemainderDensity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalProjectedRemainderDensity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma PhaseFlowOn.physicalBin_magneticField {s : Solution} {T a b I φ : ℝ}
--       (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
--       (zX : Phase) (C : ClosedConeBin) (k j : ℕ) (hJ : Icc a b⊆Icc 0 T)
--       (hI : 0<I) (hD : φ^2/2≤C.Dmin)
--       (hangle : ∀D∈Icc C.Dmin C.Dmax,DyadicWindow k j (Real.sqrt (D/2))) :
--       let X := fun t=>(prefixFlow F.flow T zX t).1
--       let V := fun t=>(prefixFlow F.flow T zX t).2
--       (∫⁻z : ConeCoordinate,ENNReal.ofReal ((z.1-z.2.1)^2*φ^2*prefixConeMagnetic s T X z^2)
--         ∂physicalBinMeasure V C (Icc a b)) ≤
--       ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
--         (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.DyadicWindow`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.PhaseFlowOn`, `OAI.RVM.Sphere`, `OAI.RVM.magneticFieldBudget`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.prefixConeMagnetic` and `OAI.RVM.prefixFlow` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.representative_regular_short_magnetic` and `OAI.RVM.Admissible.uniform_actual_magnetic_Cauchy` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalProjectedRemainderDensity.lean (declaration OAI.RVM.PhaseFlowOn.physicalBin_magneticField)

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

lemma PhaseFlowOn.physicalBin_magneticField {s : Solution} {T a b I φ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (C : ClosedConeBin) (k j : ℕ) (hJ : Icc a b⊆Icc 0 T)
    (hI : 0<I) (hD : φ^2/2≤C.Dmin)
    (hangle : ∀D∈Icc C.Dmin C.Dmax,DyadicWindow k j (Real.sqrt (D/2))) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    (∫⁻z : ConeCoordinate,ENNReal.ofReal ((z.1-z.2.1)^2*φ^2*prefixConeMagnetic s T X z^2)
      ∂physicalBinMeasure V C (Icc a b)) ≤
    ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
      (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j := by
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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
