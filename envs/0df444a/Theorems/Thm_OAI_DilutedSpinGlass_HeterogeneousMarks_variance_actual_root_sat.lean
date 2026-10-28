-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_HeterogeneousMarks_variance_actual_root_sat
-- name    : OAI.DilutedSpinGlass.HeterogeneousMarks.variance_actual_root_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:18:37.083061+00:00
-- url     : https://prove2.me/theorems/88b38c2e-1b6d-4716-a51d-402f2aabd9c7
-- title:
--   OAI.DilutedSpinGlass.HeterogeneousMarks.variance_actual_root_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.HeterogeneousMarks.variance_actual_root` of [lean/OAI/Probability/DilutedSpin/ActualRootVariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ActualRootVariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.HeterogeneousMarks`, with `open _root_.MeasureTheory ProbabilityTheory`, `open scoped NNReal ENNReal BigOperators`):
--
--   ```lean
--   theorem variance_actual_root_sat
--       (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
--       (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
--       (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
--       (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
--       (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
--       (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
--       (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
--       {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
--       (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
--       (hf : ∀ i x y, |Real.log (factor i x y)| ≤ D)
--       (hrep : ∀ h k (j : Fin k) x z y,
--         |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
--       (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
--       (E : Fin M → ℝ)
--       (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ E j)
--       (c : ℝ) :
--       variance (packRoot (fun h k x n y => root T Q m (base h k x) (rootArray n y) factor+c*n))
--         (fullRootLaw ξ μ ν r s) ≤
--         3*C^2*(r : ℝ)+3*(D+|c|)^2*(s : ℝ)+∑ j, (E j)^2/2
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.FullRootState`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.RootPath`, `OAI.DilutedSpinGlass.fullRootLaw`, `OAI.DilutedSpinGlass.packRoot`, `OAI.DilutedSpinGlass.replaceRoot`, `OAI.DilutedSpinGlass.rootArray`, `OAI.DilutedSpinGlass.rootPathMeasurable` and `OAI.DilutedSpinGlass.HeterogeneousMarks.root` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.HeterogeneousMarks.full_selected_root_concentration_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ActualRootVariance.lean (declaration OAI.DilutedSpinGlass.HeterogeneousMarks.variance_actual_root)

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
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

theorem variance_actual_root_sat
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ D)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (E : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ E j)
    (c : ℝ) :
    variance (packRoot (fun h k x n y => root T Q m (base h k x) (rootArray n y) factor+c*n))
      (fullRootLaw ξ μ ν r s) ≤
      3*C^2*(r : ℝ)+3*(D+|c|)^2*(s : ℝ)+∑ j, (E j)^2/2 := by
  sorry

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end
