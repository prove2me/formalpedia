-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_eventually_source_simultaneous_count_universal
-- name    : OAI.LipschitzHilbert.eventually_source_simultaneous_count_universal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:42:00.132998+00:00
-- url     : https://prove2.me/theorems/9a94f993-a563-4ab0-9bc1-c0f383b1c581
-- title:
--   OAI.LipschitzHilbert.eventually_source_simultaneous_count_universal: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.eventually_source_simultaneous_count_universal` of [lean/OAI/Analysis/LipschitzHilbert/Trees/SourceSimultaneousCount.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceSimultaneousCount.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert`, with `open Set MeasureTheory Filter`, `open scoped BigOperators ENNReal NNReal`):
--
--   ```lean
--   theorem eventually_source_simultaneous_count_universal (Lip : ℝ≥0)
--       (a k p t c c0 J : ℝ) (ha : 0 ≤ a) (hap : a + 1 ≤ p) (hkp : k + 1 ≤ p)
--       (ht : 2 * a + p + 1 ≤ t) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c) :
--       ∀ᶠ L : ℝ in atTop, ∀ (u : ℝ × ℝ → ℝ), LipschitzWith Lip u →
--         ∀ (ι : Type*) [Fintype ι] [DecidableEq ι], ∀ m tau : ℝ,
--         Real.exp (L ^ (9 / 10 : ℝ)) ≤ m →
--         m ≤ 2 * Real.exp (L ^ (9 / 10 : ℝ)) →
--         0 ≤ tau → tau ≤ Real.exp (-(L ^ (97 / 100 : ℝ))) →
--         ∀ (T : ι → SlopeBox) (d : ι → ℝ) (E : ι → Set (ℝ × ℝ)),
--           (∀ i, (T i).length ≤ tau) →
--           (∀ i, MeasurableSet (E i)) →
--           (∀ i, (volume.prod volume) (E i) ≠ ∞) →
--           (∀ i, ∀ w ∈ E i, (T i).radius w ≤ L ^ a) →
--           (∀ i, L ^ (-a) * (T i).length * (T i).width ≤ (volume.prod volume).real (E i)) →
--           (∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i) →
--           (∀ i, 0 ≤ d i) → (∀ i, (T i).width = m * (T i).length * d i) →
--           ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ (volume.prod volume) bad ≠ ∞ ∧
--             (volume.prod volume).real bad ≤
--               (∑ i, (T i).length * (T i).width) * Real.exp (-J * L) ∧
--             ∀ z ∉ bad, ∀ rho : ℝ, 0 < rho → ∀ I : Finset ι,
--               (∀ i ∈ I, (T i).radius z ≤ L ^ k) →
--               (∀ i ∈ I, d i ≤ rho / SourceParameters.branching L ^ 2) →
--               (∀ i ∈ I, ∀ j ∈ I,
--                 |(T i).slope - (T j).slope| ≤ SourceParameters.branching L * rho) →
--               (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
--               (I.card : ℝ) ≤ L ^ (t + 4) / 100
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.SlopeBox.radius` and `OAI.LipschitzHilbert.SourceParameters.branching` (definitions bundle `OAIQ090A000` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceSimultaneousCount.lean (declaration OAI.LipschitzHilbert.eventually_source_simultaneous_count_universal)

import Mathlib
import Definitions.Def_OAIQ090A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

theorem eventually_source_simultaneous_count_universal (Lip : ℝ≥0)
    (a k p t c c0 J : ℝ) (ha : 0 ≤ a) (hap : a + 1 ≤ p) (hkp : k + 1 ≤ p)
    (ht : 2 * a + p + 1 ≤ t) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ (u : ℝ × ℝ → ℝ), LipschitzWith Lip u →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι], ∀ m tau : ℝ,
      Real.exp (L ^ (9 / 10 : ℝ)) ≤ m →
      m ≤ 2 * Real.exp (L ^ (9 / 10 : ℝ)) →
      0 ≤ tau → tau ≤ Real.exp (-(L ^ (97 / 100 : ℝ))) →
      ∀ (T : ι → SlopeBox) (d : ι → ℝ) (E : ι → Set (ℝ × ℝ)),
        (∀ i, (T i).length ≤ tau) →
        (∀ i, MeasurableSet (E i)) →
        (∀ i, (volume.prod volume) (E i) ≠ ∞) →
        (∀ i, ∀ w ∈ E i, (T i).radius w ≤ L ^ a) →
        (∀ i, L ^ (-a) * (T i).length * (T i).width ≤ (volume.prod volume).real (E i)) →
        (∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i) →
        (∀ i, 0 ≤ d i) → (∀ i, (T i).width = m * (T i).length * d i) →
        ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ (volume.prod volume) bad ≠ ∞ ∧
          (volume.prod volume).real bad ≤
            (∑ i, (T i).length * (T i).width) * Real.exp (-J * L) ∧
          ∀ z ∉ bad, ∀ rho : ℝ, 0 < rho → ∀ I : Finset ι,
            (∀ i ∈ I, (T i).radius z ≤ L ^ k) →
            (∀ i ∈ I, d i ≤ rho / SourceParameters.branching L ^ 2) →
            (∀ i ∈ I, ∀ j ∈ I,
              |(T i).slope - (T j).slope| ≤ SourceParameters.branching L * rho) →
            (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
            (I.card : ℝ) ≤ L ^ (t + 4) / 100 := by
  sorry

end LipschitzHilbert

end

end OAI
end
