-- Prove2me | Theorems.Thm_OAI_RVM_physicalReceiverCutoff_near
-- name    : OAI.RVM.physicalReceiverCutoff_near
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:28:06.714011+00:00
-- url     : https://prove2.me/theorems/685a19b4-d746-4a82-8760-4108275699aa
-- title:
--   OAI.RVM.physicalReceiverCutoff_near: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.physicalReceiverCutoff_near` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/CutoffSourceTangent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/CutoffSourceTangent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open Set`, `open Set MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped ENNReal Topology ContDiff`):
--
--   ```lean
--   lemma physicalReceiverCutoff_near {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
--       {X V K : ℝ→Vec} (hV : Measurable V) (hK : Measurable K) (B : ClosedConeBin)
--       {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
--       {A w C p θ φ : ℝ}
--       (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A) (hw : 0<w) (hC : 0 ≤ C) (hp : 0 ≤ p) (hθ : 0 ≤ θ) (hφ : 0<φ)
--       (hsmall : B.dmax ≤ B.Dmin) (hr : 0<B.rmin) (hDlo : φ^2/2 ≤ B.Dmin)
--       (hDhi : B.Dmax ≤ 8*φ^2) (hd : B.dmax ≤ 8*θ^2)
--       (hband : ∀t∈J,w/16 ≤ ‖V t‖)
--       (Q : Set (Fin 4→ℕ))
--       (hdensity : ∀z∈physicalBinBase V B J,
--         physicalBinDensity s X V B z.1 z.2.1 z.2.2 ≤ ENNReal.ofReal (128*C*p^3*θ^2)) :
--       (∫⁻z : ConeCoordinate,physicalReceiverCutoffDensity s X V B T w Q K z
--         ∂physicalBinMeasure V B J) ≤
--       (∫⁻t in J,ENNReal.ofReal ‖K t‖)*
--         ENNReal.ofReal ((125440000*49152)*A*C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.ClosedConeBin`, `OAI.RVM.ConeCoordinate`, `OAI.RVM.EnergyPrefix`, `OAI.RVM.Sphere`, `OAI.RVM.dyadicFactor`, `OAI.RVM.physicalBinBase`, `OAI.RVM.physicalBinDensity`, `OAI.RVM.physicalBinMeasure` and `OAI.RVM.physicalReceiverCutoffDensity` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/CutoffSourceTangent.lean (declaration OAI.RVM.physicalReceiverCutoff_near)

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

lemma physicalReceiverCutoff_near {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {X V K : ℝ→Vec} (hV : Measurable V) (hK : Measurable K) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {A w C p θ φ : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A) (hw : 0<w) (hC : 0 ≤ C) (hp : 0 ≤ p) (hθ : 0 ≤ θ) (hφ : 0<φ)
    (hsmall : B.dmax ≤ B.Dmin) (hr : 0<B.rmin) (hDlo : φ^2/2 ≤ B.Dmin)
    (hDhi : B.Dmax ≤ 8*φ^2) (hd : B.dmax ≤ 8*θ^2)
    (hband : ∀t∈J,w/16 ≤ ‖V t‖)
    (Q : Set (Fin 4→ℕ))
    (hdensity : ∀z∈physicalBinBase V B J,
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ≤ ENNReal.ofReal (128*C*p^3*θ^2)) :
    (∫⁻z : ConeCoordinate,physicalReceiverCutoffDensity s X V B T w Q K z
      ∂physicalBinMeasure V B J) ≤
    (∫⁻t in J,ENNReal.ofReal ‖K t‖)*
      ENNReal.ofReal ((125440000*49152)*A*C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin)) := by
  sorry

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end
