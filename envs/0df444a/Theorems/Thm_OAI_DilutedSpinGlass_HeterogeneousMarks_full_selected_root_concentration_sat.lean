-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_HeterogeneousMarks_full_selected_root_concentration_sat
-- name    : OAI.DilutedSpinGlass.HeterogeneousMarks.full_selected_root_concentration_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:18:19.482359+00:00
-- url     : https://prove2.me/theorems/866019b3-60fa-4971-8323-92c7bb283853
-- title:
--   OAI.DilutedSpinGlass.HeterogeneousMarks.full_selected_root_concentration_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.HeterogeneousMarks.full_selected_root_concentration` of [lean/OAI/Probability/DilutedSpin/FullSelectedRawConcentration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/FullSelectedRawConcentration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.HeterogeneousMarks`, with `open _root_.MeasureTheory ProbabilityTheory Set`, `open scoped NNReal ENNReal BigOperators`):
--
--   ```lean
--   theorem full_selected_root_concentration_sat
--       (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
--       (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
--       (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
--       (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
--       (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
--       (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
--       (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
--       {B C : ℝ} (hC : 0 ≤ C)
--       (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
--       (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
--       (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
--       (hrep : ∀ h k (j : Fin k) x z y,
--         |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
--       (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
--       (fieldBound : Fin M → ℝ)
--       (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ fieldBound j)
--       {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
--       (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
--       let G := fullSelectedRawScore T Q m base sel fixed D E t
--       (∫ u in a..b, (∫ z, |G z u-∫ w, G w u ∂fullRootLaw ξ μ ν r s| ∂fullRootLaw ξ μ ν r s))/(b-a) ≤
--         4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2)/ρ+12*ρ*(s:ℝ)/(b-a)+Real.sqrt s
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.FullRootState`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.RootPath`, `OAI.DilutedSpinGlass.fullRootLaw`, `OAI.DilutedSpinGlass.replaceRoot`, `OAI.DilutedSpinGlass.rootPathMeasurable` and `OAI.DilutedSpinGlass.HeterogeneousMarks.fullSelectedRawScore` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/FullSelectedRawConcentration.lean (declaration OAI.DilutedSpinGlass.HeterogeneousMarks.full_selected_root_concentration)

import Mathlib
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

theorem full_selected_root_concentration_sat
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (fieldBound : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ fieldBound j)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let G := fullSelectedRawScore T Q m base sel fixed D E t
    (∫ u in a..b, (∫ z, |G z u-∫ w, G w u ∂fullRootLaw ξ μ ν r s| ∂fullRootLaw ξ μ ν r s))/(b-a) ≤
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2)/ρ+12*ρ*(s:ℝ)/(b-a)+Real.sqrt s := by
  sorry

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end
