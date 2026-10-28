-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_complete_physical_attachment
-- name    : OAI.ScalarConductivity.complete_physical_attachment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:56:47.10074+00:00
-- url     : https://prove2.me/theorems/af14e83b-e03c-4d1b-992c-acfaacd4b03a
-- title:
--   OAI.ScalarConductivity.complete_physical_attachment: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.complete_physical_attachment` of [lean/OAI/Analysis/Conductivity/Variational/CompletePhysicalAttachment.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Variational/CompletePhysicalAttachment.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open Set MeasureTheory Filter Topology`):
--
--   ```lean
--   theorem complete_physical_attachment (s : Fin 3 → ℝ)
--       (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
--       (a κ : Fin 3 → ℝ) (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)
--       (p : centralEnergySpace s) :
--       ∃ w : H1,w∈H10 ∧
--         H1JetOn w centralPhysical (centralFullJetCLM s p.val) ∧
--         ∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Box3`, `OAI.ScalarConductivity.CentralAmbient`, `OAI.ScalarConductivity.CentralJets`, `OAI.ScalarConductivity.CentralL2`, `OAI.ScalarConductivity.CentralTraceFields`, `OAI.ScalarConductivity.SpectralJet`, `OAI.ScalarConductivity.SpectralL2`, `OAI.ScalarConductivity.centralEnergySpace`, `OAI.ScalarConductivity.centralMeasure`, `OAI.ScalarConductivity.physicalEndRegion`, `OAI.ScalarConductivity.spectralTraceGraph` and `OAI.ScalarConductivity.torusRate` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.H1JetOn` (definitions bundle `OAIQ059C001` of this split); `OAI.ScalarConductivity.centralPhysical` (definitions bundle `OAIQ059C004` of this split); `OAI.ScalarConductivity.attachedPhysicalJet` and `OAI.ScalarConductivity.centralFullJetCLM` (definitions bundle `OAIQ059C006` of this split); `OAI.ScalarConductivity.H1`, `OAI.ScalarConductivity.H10`, `OAI.ScalarConductivity.JetFiber`, `OAI.ScalarConductivity.JetSpace`, `OAI.ScalarConductivity.R3` and `OAI.ScalarConductivity.ballMeasure` (the published bundle `Def_Conductivity`).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Variational/CompletePhysicalAttachment.lean (declaration OAI.ScalarConductivity.complete_physical_attachment)

import Mathlib
import Definitions.Def_Conductivity
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
open Set MeasureTheory Filter Topology

theorem complete_physical_attachment (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (a κ : Fin 3 → ℝ) (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)
    (p : centralEnergySpace s) :
    ∃ w : H1,w∈H10 ∧
      H1JetOn w centralPhysical (centralFullJetCLM s p.val) ∧
      ∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i) := by
  sorry

end ScalarConductivity
end

end

end OAI
end
