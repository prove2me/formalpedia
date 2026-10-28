-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_rootHistory_polarization_sat
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.rootHistory_polarization_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:21:26.233639+00:00
-- url     : https://prove2.me/theorems/3e2868a9-54b4-4e1c-a656-8f76366371c0
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.rootHistory_polarization_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.rootHistory_polarization` of [lean/OAI/Probability/DilutedSpin/RootMultileafMatrix.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/RootMultileafMatrix.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree`, `open scoped NNReal BigOperators`):
--
--   ```lean
--   lemma rootHistory_polarization_sat (hk : 0 < k)
--       (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
--       (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
--       (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
--       (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
--       (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
--       (read : Z → FinitePath Ω (L+1) → Spin)
--       (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
--       (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) (z : FullRootState Y X (Labels L Z) M) (v : Z) :
--       rootHistory S anchorLeaf T m base old read a b d spinAnchor f z v =
--         ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
--           rootExternalCoefficient S anchorLeaf T (fun i => prior i.1.1) m base old
--             (fun i x y => direction i.1.1 (read i.2 x) y)
--             (fun i x y => anchor i.1.1 (read i.2 x) y) f k z
--             ((polarizedSpec hk ε a b d spinAnchor,0),v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.FullRootState`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.RootPath`, `OAI.DilutedSpinGlass.HeterogeneousMarks.rootExternalCoefficient`, `OAI.DilutedSpinGlass.Polarization.sign`, `OAI.DilutedSpinGlass.PrescribedTree.Leaf`, `OAI.DilutedSpinGlass.UniversalDictionary.Alphabet`, `OAI.DilutedSpinGlass.UniversalDictionary.Labels`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec`, `OAI.DilutedSpinGlass.UniversalDictionary.Table`, `OAI.DilutedSpinGlass.UniversalDictionary.anchor`, `OAI.DilutedSpinGlass.UniversalDictionary.direction`, `OAI.DilutedSpinGlass.UniversalDictionary.polarizedSpec`, `OAI.DilutedSpinGlass.UniversalDictionary.prior` and `OAI.DilutedSpinGlass.UniversalDictionary.rootHistory` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.UniversalDictionary.integrable_rootHistory_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/RootMultileafMatrix.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.rootHistory_polarization)

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

omit [MeasurableSpace X] [MeasurableSpace Y] [Countable Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] in
lemma rootHistory_polarization_sat (hk : 0 < k)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ) (z : FullRootState Y X (Labels L Z) M) (v : Z) :
    rootHistory S anchorLeaf T m base old read a b d spinAnchor f z v =
      ((k:ℝ)^k / 2^k) * ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        rootExternalCoefficient S anchorLeaf T (fun i => prior i.1.1) m base old
          (fun i x y => direction i.1.1 (read i.2 x) y)
          (fun i x y => anchor i.1.1 (read i.2 x) y) f k z
          ((polarizedSpec hk ε a b d spinAnchor,0),v) := by
  sorry

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end
