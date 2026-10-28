-- Prove2me | Theorems.Thm_OAI_RVM_integrated_magneticMomentDensity_actual_before
-- name    : OAI.RVM.integrated_magneticMomentDensity_actual_before
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:26:18.62796+00:00
-- url     : https://prove2.me/theorems/ac673556-59f3-4b7a-baf8-530d43f5d094
-- title:
--   OAI.RVM.integrated_magneticMomentDensity_actual_before: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.integrated_magneticMomentDensity_actual_before` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/EquationsBefore.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/EquationsBefore.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff`, `open scoped Topology ContDiff NNReal`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`):
--
--   ```lean
--   lemma integrated_magneticMomentDensity_actual_before {d : Datum} {s : Solution} {H : ℝ}
--       (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
--       (ha : 0<a) (hT : 0<T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
--       (∫ z in ball (0:Vec) T, magneticMomentDensity (shiftedCurrent s a) T x i z) =
--         (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
--         ∫ n : Sphere, T^2*dot n.1 (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClassicalBefore`, `OAI.RVM.Sphere`, `OAI.RVM.magneticMomentDensity`, `OAI.RVM.retardedMagneticDensity`, `OAI.RVM.retardedMagneticFlux`, `OAI.RVM.shiftedCurrent` and `OAI.RVM.sphereMeasure` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Datum`, `OAI.RVM.SmoothOnFiniteHorizons`, `OAI.RVM.Solution`, `OAI.RVM.Vec` and `OAI.RVM.dot` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.classical_shifted_magnetic_physical_representation_before` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/EquationsBefore.lean (declaration OAI.RVM.integrated_magneticMomentDensity_actual_before)

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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma integrated_magneticMomentDensity_actual_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) T, magneticMomentDensity (shiftedCurrent s a) T x i z) =
      (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      ∫ n : Sphere, T^2*dot n.1 (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure := by
  sorry

end RVM

end

end OAI
end
