-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_PhysicalFiniteEndingData_corrected_pair_representative
-- name    : OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:02:53.742542+00:00
-- url     : https://prove2.me/theorems/a80b937d-411e-4194-9546-9589710636b6
-- title:
--   OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative` of [lean/OAI/Analysis/Conductivity/Branching/PhysicalBlockRepresentative.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Branching/PhysicalBlockRepresentative.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity.PhysicalFiniteEndingData`, with `open Set MeasureTheory Filter Topology Matrix`, `open scoped Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem corrected_pair_representative
--       (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
--       (w : Fin 2 → H1)
--       (hwc : ∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val))
--       (hwe : ∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) :
--       ∃ v : Coord3 → Fin 2 → ℝ,
--         (∀ᵐ y : Coord3,y∈physicalBlockRegion → v y=fun j => weakValue (w j) (WithLp.toLp 2 y)) ∧
--         (∀ᵐ y : Coord3,y∈physicalBlockRegion → ∀ i : Fin 3,∀ j : Fin 2,
--           fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i) ∧
--         volume (physicalBlockRegion \ regularRegion v (z.cartesianTensor hs) physicalBlockRegion)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Box3`, `OAI.ScalarConductivity.CentralAmbient`, `OAI.ScalarConductivity.CentralJets`, `OAI.ScalarConductivity.CentralL2`, `OAI.ScalarConductivity.CentralTraceFields`, `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.SpectralJet`, `OAI.ScalarConductivity.SpectralL2`, `OAI.ScalarConductivity.centralEnergySpace`, `OAI.ScalarConductivity.centralMeasure`, `OAI.ScalarConductivity.physicalEndRegion`, `OAI.ScalarConductivity.regularRegion`, `OAI.ScalarConductivity.spectralTraceGraph` and `OAI.ScalarConductivity.torusRate` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.H1JetOn` and `OAI.ScalarConductivity.weakValue` (definitions bundle `OAIQ059C001` of this split); `OAI.ScalarConductivity.PhysicalFiniteEndingData` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.centralPhysical` (definitions bundle `OAIQ059C004` of this split); `OAI.ScalarConductivity.centralFullJetCLM`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.cartesianTensor` and `OAI.ScalarConductivity.PhysicalFiniteEndingData.correctedEndJet` (definitions bundle `OAIQ059C006` of this split); `OAI.ScalarConductivity.physicalBlockRegion` (definitions bundle `OAIQ059C007` of this split); `OAI.ScalarConductivity.H1`, `OAI.ScalarConductivity.JetFiber`, `OAI.ScalarConductivity.JetSpace`, `OAI.ScalarConductivity.R3`, `OAI.ScalarConductivity.ballMeasure` and `OAI.ScalarConductivity.weakGradient` (the published bundle `Def_Conductivity`).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Branching/PhysicalBlockRepresentative.lean (declaration OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative)

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C006
import Definitions.Def_OAIQ059C007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

theorem corrected_pair_representative
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (w : Fin 2 → H1)
    (hwc : ∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val))
    (hwe : ∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) :
    ∃ v : Coord3 → Fin 2 → ℝ,
      (∀ᵐ y : Coord3,y∈physicalBlockRegion → v y=fun j => weakValue (w j) (WithLp.toLp 2 y)) ∧
      (∀ᵐ y : Coord3,y∈physicalBlockRegion → ∀ i : Fin 3,∀ j : Fin 2,
        fderiv ℝ (fun x => v x j) y (Pi.single i 1)=weakGradient (w j) (WithLp.toLp 2 y) i) ∧
      volume (physicalBlockRegion \ regularRegion v (z.cartesianTensor hs) physicalBlockRegion)=0 := by
  sorry

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end
