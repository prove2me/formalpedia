-- Prove2me | Theorems.Thm_OAI_RVM_physicalProjectedSource_integral_bound
-- name    : OAI.RVM.physicalProjectedSource_integral_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:27:41.109818+00:00
-- url     : https://prove2.me/theorems/2af3b360-be40-450b-a85c-4af131ef78a5
-- title:
--   OAI.RVM.physicalProjectedSource_integral_bound: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.physicalProjectedSource_integral_bound` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalProjectedRemainderDensity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalProjectedRemainderDensity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma physicalProjectedSource_integral_bound {s : Solution} {T : ℝ}
--       (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec}
--       (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
--       {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {w p θ φ c : ℝ}
--       (Q : Set (Fin 4→ℕ)) (hc : 0 ≤ c)
--       (hcut : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ c)
--       (hw : 0<w) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
--       (hr : 0<B.rmin) (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin)
--       (hDhi : B.Dmax≤8*φ^2) (hsmall : B.dmax≤B.Dmin)
--       (hband : ∀t∈J,w/16≤‖V t‖) :
--       (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z ∂physicalBinMeasure V B J)≤
--         ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))*(∫⁻z : ConeCoordinate,
--           ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal (prefixConeGood s T X z)*
--             physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)+
--         ENNReal.ofReal ((3840+94080000*c)*φ/p)*(∫⁻z : ConeCoordinate,
--           ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*ENNReal.ofReal (prefixConeMagnetic s T X z)*
--             physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.Sphere`, `OAI.RVM.dyadicFactor`, `OAI.RVM.physicalBinDensity`, `OAI.RVM.physicalBinMeasure`, `OAI.RVM.physicalProjectedSourceDensity`, `OAI.RVM.prefixConeGood` and `OAI.RVM.prefixConeMagnetic` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.projected_source_two_budget_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/PhysicalProjectedRemainderDensity.lean (declaration OAI.RVM.physicalProjectedSource_integral_bound)

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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma physicalProjectedSource_integral_bound {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec}
    (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {w p θ φ c : ℝ}
    (Q : Set (Fin 4→ℕ)) (hc : 0 ≤ c)
    (hcut : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ c)
    (hw : 0<w) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (hr : 0<B.rmin) (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin)
    (hDhi : B.Dmax≤8*φ^2) (hsmall : B.dmax≤B.Dmin)
    (hband : ∀t∈J,w/16≤‖V t‖) :
    (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z ∂physicalBinMeasure V B J)≤
      ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal (prefixConeGood s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)+
      ENNReal.ofReal ((3840+94080000*c)*φ/p)*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*ENNReal.ofReal (prefixConeMagnetic s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) := by
  sorry

end RVM

end

end OAI
end
