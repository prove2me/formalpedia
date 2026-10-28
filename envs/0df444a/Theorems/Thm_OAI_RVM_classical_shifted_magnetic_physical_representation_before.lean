-- Prove2me | Theorems.Thm_OAI_RVM_classical_shifted_magnetic_physical_representation_before
-- name    : OAI.RVM.classical_shifted_magnetic_physical_representation_before
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:23:38.224365+00:00
-- url     : https://prove2.me/theorems/0e43c3be-f778-4f4e-849f-e07a357d442a
-- title:
--   OAI.RVM.classical_shifted_magnetic_physical_representation_before (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.classical_shifted_magnetic_physical_representation_before` of [lean/OAI/Analysis/VlasovMaxwell/LocalPDE/EquationsBefore.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/EquationsBefore.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff`, `open scoped Topology ContDiff NNReal`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`):
--
--   ```lean
--   lemma classical_shifted_magnetic_physical_representation_before {d : Datum} {s : Solution} {H : ℝ}
--       (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
--       (ha : 0<a) (hT : 0<T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
--       s.B (a+T,x) i =
--         freeWave (fun y => s.B (a,y) i) (fun y => -curl (fun z => s.E (a,z)) y i) (T,x) +
--         (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
--         (4*Real.pi)⁻¹ * (∫ n : Sphere, T^2*dot n.1
--           (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure) +
--         (4*Real.pi)⁻¹ * (∫ n : Sphere,
--           T*n.1 (curlA i)*current (fun z => s.f (a,z)) (x+T • n.1) (curlB i) -
--           T*n.1 (curlB i)*current (fun z => s.f (a,z)) (x+T • n.1) (curlA i) ∂sphereMeasure)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClassicalBefore`, `OAI.RVM.Sphere`, `OAI.RVM.curlA`, `OAI.RVM.curlB`, `OAI.RVM.freeWave`, `OAI.RVM.retardedMagneticDensity`, `OAI.RVM.retardedMagneticFlux` and `OAI.RVM.sphereMeasure` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Datum`, `OAI.RVM.Phase`, `OAI.RVM.SmoothOnFiniteHorizons`, `OAI.RVM.Solution`, `OAI.RVM.Vec`, `OAI.RVM.curl`, `OAI.RVM.current` and `OAI.RVM.dot` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Magnetic.classical_magnetic_gradient_volterra_bound`, `OAI.RVM.SmoothClassicalPrefix.physical_vectors`, `OAI.RVM.SmoothClassicalPrefix.retarded_force_source_polar` and `OAI.RVM.classical_fields_curvature_volterra_bound` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/LocalPDE/EquationsBefore.lean (declaration OAI.RVM.classical_shifted_magnetic_physical_representation_before)

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

lemma classical_shifted_magnetic_physical_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    s.B (a+T,x) i =
      freeWave (fun y => s.B (a,y) i) (fun y => -curl (fun z => s.E (a,z)) y i) (T,x) +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      (4*Real.pi)⁻¹ * (∫ n : Sphere, T^2*dot n.1
        (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure) +
      (4*Real.pi)⁻¹ * (∫ n : Sphere,
        T*n.1 (curlA i)*current (fun z => s.f (a,z)) (x+T • n.1) (curlB i) -
        T*n.1 (curlB i)*current (fun z => s.f (a,z)) (x+T • n.1) (curlA i) ∂sphereMeasure) := by
  sorry

end RVM

end

end OAI
end
