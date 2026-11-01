-- Prove2me | Theorems.Thm_OAI_JointDickman_active_high_addition_class_bound_jd
-- name    : OAI.JointDickman.active_high_addition_class_bound_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:32:32.87109+00:00
-- url     : https://prove2.me/theorems/f639d80d-750c-46c4-aab5-b77509ab11a8
-- title:
--   OAI.JointDickman.active_high_addition_class_bound_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.active_high_addition_class_bound` of [lean/OAI/NumberTheory/JointDickman/Amplification/LargeHighClass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/LargeHighClass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter Classical`, `open scoped Topology`):
--
--   ```lean
--   theorem active_high_addition_class_bound_jd
--       (hFord : PublishedInputs.FordUpperSieveInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ τ ε : ℝ}
--       (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
--       (hΔ : 0 < Δ) (hgap : 2*Δ < g)
--       (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
--         ∀ (C : ℝ) (A : Finset ℕ) (e j b d : ℕ),
--           A ⊆ auxiliaryPrimes B → (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
--           0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B → e.Coprime j →
--           (e : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) → (j : ℝ) ≤ (B : ℝ)^2 →
--           tiltedRegularSubsetCount B L τ C A (activeHighAdditionClass B L k τ C Δ A e j b d) ≤
--             K/(j : ℝ)*Real.exp
--               (largeAvailabilityExponent g Δ δ τ ε (auxiliaryLogLength B) d*auxiliaryLogLength B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.activeHighAdditionClass`, `OAI.JointDickman.auxiliaryCutoff`, `OAI.JointDickman.auxiliaryLogLength`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.largeAvailabilityExponent`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput` and `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.tiltedRegularSubsetCount` (definitions bundle `OAIQ083J003` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.tiltedCandidatePairCount_bound_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/LargeHighClass.lean (declaration OAI.JointDickman.active_high_addition_class_bound)

import Mathlib
import Definitions.Def_OAIQ083J003

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem active_high_addition_class_bound_jd
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ τ ε : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (C : ℝ) (A : Finset ℕ) (e j b d : ℕ),
        A ⊆ auxiliaryPrimes B → (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B → e.Coprime j →
        (e : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) → (j : ℝ) ≤ (B : ℝ)^2 →
        tiltedRegularSubsetCount B L τ C A (activeHighAdditionClass B L k τ C Δ A e j b d) ≤
          K/(j : ℝ)*Real.exp
            (largeAvailabilityExponent g Δ δ τ ε (auxiliaryLogLength B) d*auxiliaryLogLength B) := by
  sorry

end JointDickman

end OAI
end
