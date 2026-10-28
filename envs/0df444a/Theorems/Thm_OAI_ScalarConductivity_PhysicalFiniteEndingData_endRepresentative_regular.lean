-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_PhysicalFiniteEndingData_endRepresentative_regular
-- name    : OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative_regular
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:54:13.104951+00:00
-- url     : https://prove2.me/theorems/c180f844-6d00-43b4-8701-00662d0d3516
-- title:
--   OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative_regular (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative_regular` of [lean/OAI/Analysis/Conductivity/Variational/CentralCorrectedRepresentative.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Variational/CentralCorrectedRepresentative.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity.PhysicalFiniteEndingData`, with `open Set MeasureTheory Filter Topology Matrix`, `open scoped Matrix.Norms.Elementwise`):
--
--   ```lean
--   lemma endRepresentative_regular
--       (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
--       (hS : ∀ i y,(variableEndTensor (fun i => branchSplicedTensor i (z.ending i)) z.compression i y).IsSymm)
--       (i : Fin 3) : ∀ᵐ y : Coord3,y∈physicalEndRegion i →
--         y∈regularRegion (z.endRepresentative i)
--           (fun y => ⟨variableEndTensor (fun i => branchSplicedTensor i (z.ending i)) z.compression i y,hS i y⟩) univ
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Box3`, `OAI.ScalarConductivity.CentralAmbient`, `OAI.ScalarConductivity.CentralJets`, `OAI.ScalarConductivity.CentralL2`, `OAI.ScalarConductivity.CentralTraceFields`, `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.Mat3`, `OAI.ScalarConductivity.SpectralJet`, `OAI.ScalarConductivity.SpectralL2`, `OAI.ScalarConductivity.centralEnergySpace`, `OAI.ScalarConductivity.centralMeasure`, `OAI.ScalarConductivity.physicalEndRegion`, `OAI.ScalarConductivity.regularRegion`, `OAI.ScalarConductivity.spectralTraceGraph` and `OAI.ScalarConductivity.torusRate` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.TorusL2` and `OAI.ScalarConductivity.torusPoissonFlowMeasureSpace` (definitions bundle `OAIQ059C001` of this split); `OAI.ScalarConductivity.PhysicalFiniteEndingData`, `OAI.ScalarConductivity.branchSplicedTensor`, `OAI.ScalarConductivity.centralT`, `OAI.ScalarConductivity.torusSpectralSynthesis`, `OAI.ScalarConductivity.variableEndTensor` and `OAI.ScalarConductivity.PhysicalFiniteEndingData.compression` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative` (definitions bundle `OAIQ059C006` of this split).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_pair_representative` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Variational/CentralCorrectedRepresentative.lean (declaration OAI.ScalarConductivity.PhysicalFiniteEndingData.endRepresentative_regular)

import Mathlib
import Definitions.Def_OAIQ059C006

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
open scoped Matrix.Norms.Elementwise

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma endRepresentative_regular
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hS : ∀ i y,(variableEndTensor (fun i => branchSplicedTensor i (z.ending i)) z.compression i y).IsSymm)
    (i : Fin 3) : ∀ᵐ y : Coord3,y∈physicalEndRegion i →
      y∈regularRegion (z.endRepresentative i)
        (fun y => ⟨variableEndTensor (fun i => branchSplicedTensor i (z.ending i)) z.compression i y,hS i y⟩) univ := by
  sorry

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
end
