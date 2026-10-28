-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_PhysicalFiniteEndingData_scalar_pair_green_exists
-- name    : OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:01:40.286433+00:00
-- url     : https://prove2.me/theorems/88c9b6cc-423e-46a1-95ab-0918e3e3d2d7
-- title:
--   OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists` of [lean/OAI/Analysis/Conductivity/Scalarization/PhysicalScalarization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Scalarization/PhysicalScalarization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity.PhysicalFiniteEndingData`, with `open Set MeasureTheory Filter Topology Matrix`, `open scoped Matrix.Norms.Elementwise ENNReal`):
--
--   ```lean
--   theorem scalar_pair_green_exists
--       (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
--       ∃ (σ : Coord3 → ℝ) (c C : ℝ) (w q : Fin 2 → H1),
--         Measurable σ ∧ MemLp σ ∞ (volume.restrict physicalOpenBlock) ∧
--         0 < c ∧ c<C ∧ (∀ᵐ y∂volume.restrict physicalOpenBlock,σ y∈Icc c C) ∧
--         (∀ j,q j∈H10) ∧
--         (∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val)) ∧
--         (∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) ∧
--         (∃ Z : VoltageJetSpace volume physicalOpenBlock,
--           Z-originalPairVoltageJet physicalOpenBlock w∈zeroVoltageJets volume physicalOpenBlock ∧
--           ∀ j,(q j-w j).val=voltageOriginalJetCLM physicalOpenBlock_open.measurableSet j
--             (Z-originalPairVoltageJet physicalOpenBlock w)) ∧
--         ∀ j (h : H1),(∫ y in physicalOpenBlock,σ y*(originalPiGradient (q j) y ⬝ᵥ
--           originalPiGradient h y))=constantTerminalFluxCLM (centralBasisSlopes j) h
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Box3`, `OAI.ScalarConductivity.CentralAmbient`, `OAI.ScalarConductivity.CentralJets`, `OAI.ScalarConductivity.CentralL2`, `OAI.ScalarConductivity.CentralTraceFields`, `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.SpectralJet`, `OAI.ScalarConductivity.SpectralL2`, `OAI.ScalarConductivity.centralBasisSlopes`, `OAI.ScalarConductivity.centralEnergySpace`, `OAI.ScalarConductivity.centralMeasure`, `OAI.ScalarConductivity.physicalEndRegion`, `OAI.ScalarConductivity.spectralTraceGraph` and `OAI.ScalarConductivity.torusRate` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.FieldVector` and `OAI.ScalarConductivity.H1JetOn` (definitions bundle `OAIQ059C001` of this split); `OAI.ScalarConductivity.originalPiGradient` (definitions bundle `OAIQ059C002` of this split); `OAI.ScalarConductivity.PhysicalFiniteEndingData`, `OAI.ScalarConductivity.constantTerminalFluxCLM` and `OAI.ScalarConductivity.physicalOpenBlock` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.VoltageJetSpace` and `OAI.ScalarConductivity.centralPhysical` (definitions bundle `OAIQ059C004` of this split); `OAI.ScalarConductivity.centralFullJetCLM` and `OAI.ScalarConductivity.PhysicalFiniteEndingData.correctedEndJet` (definitions bundle `OAIQ059C006` of this split); `OAI.ScalarConductivity.originalPairVoltageJet`, `OAI.ScalarConductivity.physicalOpenBlock_open` and `OAI.ScalarConductivity.voltageOriginalJetCLM` (definitions bundle `OAIQ059C007` of this split); `OAI.ScalarConductivity.zeroVoltageJets` (definitions bundle `OAIQ059C008` of this split); `OAI.ScalarConductivity.H1`, `OAI.ScalarConductivity.H10`, `OAI.ScalarConductivity.JetFiber`, `OAI.ScalarConductivity.JetSpace`, `OAI.ScalarConductivity.R3` and `OAI.ScalarConductivity.ballMeasure` (the published bundle `Def_Conductivity`).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.boundedRootSources_nonempty` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Scalarization/PhysicalScalarization.lean (declaration OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists)

import Mathlib
import Definitions.Def_Conductivity
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
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

theorem scalar_pair_green_exists
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ (σ : Coord3 → ℝ) (c C : ℝ) (w q : Fin 2 → H1),
      Measurable σ ∧ MemLp σ ∞ (volume.restrict physicalOpenBlock) ∧
      0 < c ∧ c<C ∧ (∀ᵐ y∂volume.restrict physicalOpenBlock,σ y∈Icc c C) ∧
      (∀ j,q j∈H10) ∧
      (∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val)) ∧
      (∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) ∧
      (∃ Z : VoltageJetSpace volume physicalOpenBlock,
        Z-originalPairVoltageJet physicalOpenBlock w∈zeroVoltageJets volume physicalOpenBlock ∧
        ∀ j,(q j-w j).val=voltageOriginalJetCLM physicalOpenBlock_open.measurableSet j
          (Z-originalPairVoltageJet physicalOpenBlock w)) ∧
      ∀ j (h : H1),(∫ y in physicalOpenBlock,σ y*(originalPiGradient (q j) y ⬝ᵥ
        originalPiGradient h y))=constantTerminalFluxCLM (centralBasisSlopes j) h := by
  sorry

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end
