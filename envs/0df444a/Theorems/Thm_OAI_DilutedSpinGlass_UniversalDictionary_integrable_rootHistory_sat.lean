-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_integrable_rootHistory_sat
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.integrable_rootHistory_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:20:51.524122+00:00
-- url     : https://prove2.me/theorems/b6edb7b1-463d-45d2-aa23-381983b7efbc
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.integrable_rootHistory_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.integrable_rootHistory` of [lean/OAI/Probability/DilutedSpin/ConcreteHistory.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ConcreteHistory.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree`, `open scoped NNReal BigOperators`):
--
--   ```lean
--   lemma integrable_rootHistory_sat (hk : 0 < k) :
--       Integrable (fun z : FullRootState Y X (Labels L Z) M × Z =>
--         rootHistory S anchorLeaf T m base old read a b d spinAnchor f z.1 z.2)
--         ((fullRootLaw ξ μ ν rate score).prod τ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.FullRootState`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.RootPath`, `OAI.DilutedSpinGlass.fullRootLaw`, `OAI.DilutedSpinGlass.rootPathMeasurable`, `OAI.DilutedSpinGlass.PrescribedTree.Leaf`, `OAI.DilutedSpinGlass.UniversalDictionary.Alphabet`, `OAI.DilutedSpinGlass.UniversalDictionary.Labels`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec`, `OAI.DilutedSpinGlass.UniversalDictionary.rootHistory` and `OAI.DilutedSpinGlass.UniversalDictionary.specMeasurable` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ConcreteHistory.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.integrable_rootHistory)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M r k : ℕ}

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Labels L Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (rate score : ℝ≥0)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)

include hb hm hmono hpos hroot hend hB hf

lemma integrable_rootHistory_sat (hk : 0 < k) :
    Integrable (fun z : FullRootState Y X (Labels L Z) M × Z =>
      rootHistory S anchorLeaf T m base old read a b d spinAnchor f z.1 z.2)
      ((fullRootLaw ξ μ ν rate score).prod τ) := by
  sorry

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end
