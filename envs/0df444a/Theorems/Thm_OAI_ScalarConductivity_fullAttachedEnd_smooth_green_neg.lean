-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_fullAttachedEnd_smooth_green_neg
-- name    : OAI.ScalarConductivity.fullAttachedEnd_smooth_green_neg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:57:27.894602+00:00
-- url     : https://prove2.me/theorems/9060f744-d8b8-45bd-9b11-e7ba1fac1c9d
-- title:
--   OAI.ScalarConductivity.fullAttachedEnd_smooth_green_neg: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.fullAttachedEnd_smooth_green_neg` of [lean/OAI/Analysis/Conductivity/Flux/PhysicalEndSmoothGreen.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Flux/PhysicalEndSmoothGreen.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open Set MeasureTheory Filter Topology UnitAddTorus Matrix`, `open scoped ENNReal`):
--
--   ```lean
--   lemma fullAttachedEnd_smooth_green_neg (s : Fin 3 → ℝ)
--       (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
--       (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
--       {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
--       {a l r R : ℝ} (ha : a<0) (hlr : l < r) (hR : a*(l-r)=R)
--       (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
--       (∫ y in sourceClosedCollarBand l r,fullAttachedEndGradient s f a r κ y ⬝ᵥ
--         (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y))=
--         angularArea*(inner ℝ (spectralGraphWeight (torusRate s) f)
--           (spectralGraphWeight (torusRate s) (smoothCollarTrace s r hφ))-
--         κ*spectralGraphMean (torusRate s) (smoothCollarTrace s r hφ)+
--         cylinderTerminalFlux s κ R f (smoothCollarTrace s l hφ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.SpectralJet`, `OAI.ScalarConductivity.SpectralL2`, `OAI.ScalarConductivity.angularArea`, `OAI.ScalarConductivity.sourceClosedCollarBand`, `OAI.ScalarConductivity.spectralTraceGraph` and `OAI.ScalarConductivity.torusRate` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.physicalTestCovector` (definitions bundle `OAIQ059C001` of this split); `OAI.ScalarConductivity.spectralGraphMean` and `OAI.ScalarConductivity.spectralGraphWeight` (definitions bundle `OAIQ059C003` of this split); `OAI.ScalarConductivity.smoothCollarTrace` (definitions bundle `OAIQ059C004` of this split); `OAI.ScalarConductivity.attachedCollarTensor` and `OAI.ScalarConductivity.fullAttachedEndGradient` (definitions bundle `OAIQ059C006` of this split); `OAI.ScalarConductivity.cylinderTerminalFlux` (definitions bundle `OAIQ059C007` of this split).
--
--   **Used by.** The proofs of `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green` and `OAI.ScalarConductivity.PhysicalFiniteEndingData.scalar_pair_green_exists` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Flux/PhysicalEndSmoothGreen.lean (declaration OAI.ScalarConductivity.fullAttachedEnd_smooth_green_neg)

import Mathlib
import Definitions.Def_OAIQ059C006
import Definitions.Def_OAIQ059C007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma fullAttachedEnd_smooth_green_neg (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a l r R : ℝ} (ha : a<0) (hlr : l < r) (hR : a*(l-r)=R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∫ y in sourceClosedCollarBand l r,fullAttachedEndGradient s f a r κ y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) f)
        (spectralGraphWeight (torusRate s) (smoothCollarTrace s r hφ))-
      κ*spectralGraphMean (torusRate s) (smoothCollarTrace s r hφ)+
      cylinderTerminalFlux s κ R f (smoothCollarTrace s l hφ)) := by
  sorry

end ScalarConductivity

end
end

end OAI
end
