-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_splicedAttached_energy_ae
-- name    : OAI.ScalarConductivity.splicedAttached_energy_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:04:43.389233+00:00
-- url     : https://prove2.me/theorems/9b0df17b-cef5-4c36-ab7a-b077ab0bce15
-- title:
--   OAI.ScalarConductivity.splicedAttached_energy_ae: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.splicedAttached_energy_ae` of [lean/OAI/Analysis/Conductivity/Flux/AttachedSplicedGreen.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Flux/AttachedSplicedGreen.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open Set Filter Topology MeasureTheory Matrix UnitAddTorus`, `open scoped ENNReal`):
--
--   ```lean
--   lemma splicedAttached_energy_ae
--       (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
--       (j : Fin 2) (φ : Coord3 → ℝ) {a b l r : ℝ} (ha : a≠0)
--       (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (ht : ∀ t∈Ioo l r,0<a*(t-b)) :
--       (fun y => splicedAttachedGradient f i z j a b y ⬝ᵥ
--          (variableCollarTensor (branchSplicedTensor i z) a b y*ᵥphysicalTestCovector φ y))=ᵐ[
--            volume.restrict (sourceClosedCollarBand l r)]
--         fun y => fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y ⬝ᵥ
--           (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y)+
--             attachedPeriodicFlux (branchFluxCorrection i z j) a b y ⬝ᵥphysicalTestCovector φ y
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.SpectralJet`, `OAI.ScalarConductivity.SpectralL2`, `OAI.ScalarConductivity.centralBasisSlopes`, `OAI.ScalarConductivity.sourceClosedCollarBand`, `OAI.ScalarConductivity.spectralTraceGraph` and `OAI.ScalarConductivity.torusRate` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.TorusL2`, `OAI.ScalarConductivity.branchNormalize`, `OAI.ScalarConductivity.physicalTestCovector` and `OAI.ScalarConductivity.torusPoissonFlowMeasureSpace` (definitions bundle `OAIQ059C001` of this split); `OAI.ScalarConductivity.TorusEndingData`, `OAI.ScalarConductivity.branchSplicedTensor`, `OAI.ScalarConductivity.torusSpectralSynthesis` and `OAI.ScalarConductivity.variableCollarTensor` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.attachedCollarTensor`, `OAI.ScalarConductivity.attachedPeriodicFlux`, `OAI.ScalarConductivity.branchFluxCorrection` and `OAI.ScalarConductivity.fullAttachedEndGradient` (definitions bundle `OAIQ059C006` of this split); `OAI.ScalarConductivity.splicedAttachedGradient` (definitions bundle `OAIQ059C008` of this split).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Flux/AttachedSplicedGreen.lean (declaration OAI.ScalarConductivity.splicedAttached_energy_ae)

import Mathlib
import Definitions.Def_OAIQ059C008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped ENNReal

local instance attachedSplicedGreenMeasureSpace_r58301d_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {s : Fin 3 → ℝ} (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))

lemma splicedAttached_energy_ae
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (φ : Coord3 → ℝ) {a b l r : ℝ} (ha : a≠0)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (ht : ∀ t∈Ioo l r,0<a*(t-b)) :
    (fun y => splicedAttachedGradient f i z j a b y ⬝ᵥ
       (variableCollarTensor (branchSplicedTensor i z) a b y*ᵥphysicalTestCovector φ y))=ᵐ[
         volume.restrict (sourceClosedCollarBand l r)]
      fun y => fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y ⬝ᵥ
        (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y)+
          attachedPeriodicFlux (branchFluxCorrection i z j) a b y ⬝ᵥphysicalTestCovector φ y := by
  sorry

end ScalarConductivity

end
end

end OAI
end
