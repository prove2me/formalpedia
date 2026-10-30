-- Prove2me | Theorems.Thm_OAI_Falconer_exists_far_data_bound
-- name    : OAI.Falconer.exists_far_data_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:49:11.214627+00:00
-- url     : https://prove2.me/theorems/dfc5d284-0463-4b7c-8de3-955d6ff231c3
-- title:
--   OAI.Falconer.exists_far_data_bound: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.exists_far_data_bound` of [lean/OAI/MeasureTheory/Falconer/Estimates/FarDataBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/FarDataBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory`, `open scoped ENNReal ContDiff`):
--
--   ```lean
--    theorem exists_far_data_bound
--       (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
--       (m K L M q : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
--       (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
--       {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
--       ∃ B C Cerr : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ 0 ≤ Cerr ∧
--         ∀ (D : JetStateFarData m B), D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
--         -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss →
--         ∀ (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3)),
--         ENNReal.ofReal D.prefactor *
--           (∫⁻ z in farDisplacementRegion (m+3) D.a D.h,
--             ENNReal.ofReal ‖D.kernel f g w₀ Ψ z‖ ∂D.originalMeasure) ≤
--           (∑ b ∈ Finset.Icc (D.a+9) (D.h+6), D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b) +
--           ENNReal.ofReal D.prefactor *
--             (2+((Finset.Icc (D.a+9) (D.h+6)).card:ℝ≥0∞)) *
--             ENNReal.ofReal (Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss))*D.originalMeasure univ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.DescriptorJetSymbol`, `OAI.Falconer.JetStateFarData`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.JetStateFarData.collisionTerm`, `OAI.Falconer.JetStateFarData.kernel`, `OAI.Falconer.JetStateFarData.originalMeasure` and `OAI.Falconer.JetStateFarData.prefactor` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedGnomonicSurface`, `OAI.Falconer.PublishedQuadraticStationary` and `OAI.Falconer.farDisplacementRegion` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI_Falconer_exists_policy_far_recurrence` and `OAI.Falconer.exists_policy_recursion_bounds` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/FarDataBound.lean (declaration OAI.Falconer.exists_far_data_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

 theorem exists_far_data_bound
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M q : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C Cerr : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ 0 ≤ Cerr ∧
      ∀ (D : JetStateFarData m B), D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss →
      ∀ (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3)),
      ENNReal.ofReal D.prefactor *
        (∫⁻ z in farDisplacementRegion (m+3) D.a D.h,
          ENNReal.ofReal ‖D.kernel f g w₀ Ψ z‖ ∂D.originalMeasure) ≤
        (∑ b ∈ Finset.Icc (D.a+9) (D.h+6), D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b) +
        ENNReal.ofReal D.prefactor *
          (2+((Finset.Icc (D.a+9) (D.h+6)).card:ℝ≥0∞)) *
          ENNReal.ofReal (Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss))*D.originalMeasure univ := by
  sorry

end Falconer

end OAI
end
