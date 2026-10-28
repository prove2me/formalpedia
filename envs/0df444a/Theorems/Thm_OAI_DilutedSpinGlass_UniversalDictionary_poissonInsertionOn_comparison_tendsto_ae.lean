-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_poissonInsertionOn_comparison_tendsto_ae
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.poissonInsertionOn_comparison_tendsto_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T07:59:19.24705+00:00
-- url     : https://prove2.me/theorems/4cb37aba-fe13-4b41-99b4-ba4ac142fe57
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.poissonInsertionOn_comparison_tendsto_ae: intermediate lemma from OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DilutedSpinGlass.mezard_parisi`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mézard–Parisi formula for diluted spin glasses (result family 221)*, OpenAI Math Release, September 23, 2026, result family 221, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.poissonInsertionOn_comparison_tendsto_ae` of [lean/OAI/Probability/DilutedSpin/DilutedSpin/UpperInsertion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/UpperInsertion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory Filter`, `open scoped Topology NNReal BigOperators`, `open ConcreteReservoir`):
--
--   ```lean
--   lemma poissonInsertionOn_comparison_tendsto_ae
--       {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
--       {p : ℕ} (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
--       (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
--       (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
--       (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L))
--       (μ : (k : ℕ) → Measure (X k)) [∀ k,IsProbabilityMeasure (μ k)]
--       (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) (hFm : ∀ k,Measurable (F k))
--       {B D : ℝ} (hB : 0≤B) (hD : 0≤D)
--       (hF : ∀ k,∀ᵐ x ∂μ k,∀ s,|F k x s|≤B+D*k) (ρ : ℝ≥0) :
--       Tendsto (fun L => limsup (fun n => ∫ k,
--         |(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F k x) ∂μ k)-
--           (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
--             (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F k x)) ∂μ k)|
--         ∂poissonMeasure ρ) atTop) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FiniteLaw.spinLog`, `OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec`, `OAI.DilutedSpinGlass.UniversalDictionary.gridExponents`, `OAI.DilutedSpinGlass.UniversalDictionary.reservoirInsertionOn` and `OAI.DilutedSpinGlass.UniversalDictionary.reservoirTrialLaw` (definitions bundle `OAIQ041D000` of this split); `OAI.DilutedSpinGlass.Model`, `OAI.DilutedSpinGlass.Spin` and `OAI.DilutedSpinGlass.trialLog` (the published bundle `Def_DilutedSpin`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.mezard_parisi` of this split imports it.
-- source:
--   OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 221; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/UpperInsertion.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.poissonInsertionOn_comparison_tendsto_ae)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

namespace UniversalDictionary
open ConcreteReservoir

lemma poissonInsertionOn_comparison_tendsto_ae
    {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
    {p : ℕ} (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L,Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L,FullShapeControl M C H L (Ns L) (us L))
    (μ : (k : ℕ) → Measure (X k)) [∀ k,IsProbabilityMeasure (μ k)]
    (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) (hFm : ∀ k,Measurable (F k))
    {B D : ℝ} (hB : 0≤B) (hD : 0≤D)
    (hF : ∀ k,∀ᵐ x ∂μ k,∀ s,|F k x s|≤B+D*k) (ρ : ℝ≥0) :
    Tendsto (fun L => limsup (fun n => ∫ k,
      |(∫ x,reservoirInsertionOn M C H (Ns L n+1) L (us L n) (F k x) ∂μ k)-
        (∫ x,trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F k x)) ∂μ k)|
      ∂poissonMeasure ρ) atTop) atTop (𝓝 0) := by
  sorry

end UniversalDictionary
end DilutedSpinGlass

end

end OAI
end
