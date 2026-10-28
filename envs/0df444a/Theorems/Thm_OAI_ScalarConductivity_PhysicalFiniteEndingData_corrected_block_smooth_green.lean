-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_PhysicalFiniteEndingData_corrected_block_smooth_green
-- name    : OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:58:02.738181+00:00
-- url     : https://prove2.me/theorems/fe6c2b89-409c-4444-b87b-7292e693a1e4
-- title:
--   OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green` of [lean/OAI/Analysis/Conductivity/Flux/PhysicalSplicedGreen.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Flux/PhysicalSplicedGreen.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity.PhysicalFiniteEndingData`, with `open Set MeasureTheory Filter Topology Matrix`):
--
--   ```lean
--   lemma corrected_block_smooth_green
--       (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
--       (j : Fin 2) (w : H1) (hwc : H1JetOn w centralPhysical (centralFullJetCLM s (z.p j).val))
--       (hwe : ∀ i,H1JetOn w (physicalEndRegion i) (z.correctedEndJet j i))
--       {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
--       (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
--         (variableBlockTensor z.flatTensor z.compression y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
--         constantTerminalFluxCLM (centralBasisSlopes j) (piSmoothH1 hφ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Box3`, `OAI.ScalarConductivity.CentralAmbient`, `OAI.ScalarConductivity.CentralJets`, `OAI.ScalarConductivity.CentralL2`, `OAI.ScalarConductivity.CentralTraceFields`, `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.SpectralJet`, `OAI.ScalarConductivity.SpectralL2`, `OAI.ScalarConductivity.centralBasisSlopes`, `OAI.ScalarConductivity.centralEnergySpace`, `OAI.ScalarConductivity.centralMeasure`, `OAI.ScalarConductivity.physicalEndRegion`, `OAI.ScalarConductivity.piSmoothH1`, `OAI.ScalarConductivity.spectralTraceGraph` and `OAI.ScalarConductivity.torusRate` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.H1JetOn` (definitions bundle `OAIQ059C001` of this split); `OAI.ScalarConductivity.originalPiGradient` (definitions bundle `OAIQ059C002` of this split); `OAI.ScalarConductivity.PhysicalFiniteEndingData`, `OAI.ScalarConductivity.constantTerminalFluxCLM`, `OAI.ScalarConductivity.variableBlockTensor`, `OAI.ScalarConductivity.PhysicalFiniteEndingData.compression` and `OAI.ScalarConductivity.PhysicalFiniteEndingData.flatTensor` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.centralPhysical` (definitions bundle `OAIQ059C004` of this split); `OAI.ScalarConductivity.centralFullJetCLM` and `OAI.ScalarConductivity.PhysicalFiniteEndingData.correctedEndJet` (definitions bundle `OAIQ059C006` of this split); `OAI.ScalarConductivity.physicalBlockRegion` (definitions bundle `OAIQ059C007` of this split); `OAI.ScalarConductivity.H1`, `OAI.ScalarConductivity.JetFiber`, `OAI.ScalarConductivity.JetSpace`, `OAI.ScalarConductivity.R3` and `OAI.ScalarConductivity.ballMeasure` (the published bundle `Def_Conductivity`).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Flux/PhysicalSplicedGreen.lean (declaration OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green)

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

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma corrected_block_smooth_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (w : H1) (hwc : H1JetOn w centralPhysical (centralFullJetCLM s (z.p j).val))
    (hwe : ∀ i,H1JetOn w (physicalEndRegion i) (z.correctedEndJet j i))
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
      (variableBlockTensor z.flatTensor z.compression y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      constantTerminalFluxCLM (centralBasisSlopes j) (piSmoothH1 hφ) := by
  sorry

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
end
