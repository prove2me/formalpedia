-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_HeterogeneousMarks_independentInsertion_tail_sat
-- name    : OAI.DilutedSpinGlass.HeterogeneousMarks.independentInsertion_tail_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:18:12.901621+00:00
-- url     : https://prove2.me/theorems/1d268946-8360-4212-971e-0e2d9be9fc0e
-- title:
--   OAI.DilutedSpinGlass.HeterogeneousMarks.independentInsertion_tail_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.HeterogeneousMarks.independentInsertion_tail` of [lean/OAI/Probability/DilutedSpin/SameInsertionAverage.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/SameInsertionAverage.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.HeterogeneousMarks`, with `open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir`, `open scoped BigOperators`):
--
--   ```lean
--   lemma independentInsertion_tail_sat (hm : Monotone q) (hpos : ∀ j, 0 ≤ q j)
--       (hnz : ∀ j : Fin (L+1), q j.succ≠0) (hroot : q 0=0) (hend : q (Fin.last (L+1))=1)
--       (a : ℕ) (F : (Fin a → Spin) → ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀ s, |F s|≤C)
--       (z : Fin a → FullRootState Y X I M × Site N) (K : ℕ) :
--       |(independentInsertion T Q (fun i => q i.succ) base old V a F z-C)-
--         ∑ k∈Finset.range K, (-1:ℝ)^k/(k+1)*
--           qExpect q (fun R => independentTreeCoefficient R T Q (fun i => q i.succ) base old V a
--             (fun s => normalizedInsertion C (F s)) z) k (single (L+1))*insertionRadius C^(k+1)| ≤
--         ∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.FullRootState`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.RootPath`, `OAI.DilutedSpinGlass.insertionRadius`, `OAI.DilutedSpinGlass.normalizedInsertion`, `OAI.DilutedSpinGlass.ConcreteReservoir.Site`, `OAI.DilutedSpinGlass.HeterogeneousMarks.independentInsertion`, `OAI.DilutedSpinGlass.HeterogeneousMarks.independentTreeCoefficient`, `OAI.DilutedSpinGlass.PrescribedTree.qExpect` and `OAI.DilutedSpinGlass.PrescribedTree.single` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/SameInsertionAverage.lean (declaration OAI.DilutedSpinGlass.HeterogeneousMarks.independentInsertion_tail)

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
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

variable (q : Fin (L+2) → ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentInsertion_tail_sat (hm : Monotone q) (hpos : ∀ j, 0 ≤ q j)
    (hnz : ∀ j : Fin (L+1), q j.succ≠0) (hroot : q 0=0) (hend : q (Fin.last (L+1))=1)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀ s, |F s|≤C)
    (z : Fin a → FullRootState Y X I M × Site N) (K : ℕ) :
    |(independentInsertion T Q (fun i => q i.succ) base old V a F z-C)-
      ∑ k∈Finset.range K, (-1:ℝ)^k/(k+1)*
        qExpect q (fun R => independentTreeCoefficient R T Q (fun i => q i.succ) base old V a
          (fun s => normalizedInsertion C (F s)) z) k (single (L+1))*insertionRadius C^(k+1)| ≤
      ∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
  sorry
end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end
