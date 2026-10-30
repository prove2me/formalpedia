-- Prove2me | Theorems.Thm_OAI_Falconer_TwoProjectionPieces_odd_original_caps_partition
-- name    : OAI.Falconer.TwoProjectionPieces.odd_original_caps_partition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:45:24.971931+00:00
-- url     : https://prove2.me/theorems/ee07e616-ad5f-4729-95e2-48f20f533abb
-- title:
--   OAI.Falconer.TwoProjectionPieces.odd_original_caps_partition: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.TwoProjectionPieces.odd_original_caps_partition` of [lean/OAI/MeasureTheory/Falconer/Angular/OddOriginalCaps.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Angular/OddOriginalCaps.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer.TwoProjectionPieces`, with `open Set MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem odd_original_caps_partition (p : TwoProjectionPieces f ε)
--       (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
--       (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
--       (hα : (h:ℝ)+3/2 < α) (hα' : α < (h:ℝ)+2)
--       {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
--       ∃ Γ : ℕ → Set (Space d × Space d),
--         (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
--         0 < ((p.left : Measure (Space d)).prod (p.right : Measure (Space d))) (⋂ N, Γ N) ∧
--         (∀ N, Γ N ⊆ supportPair p.left p.right) ∧
--         CapAvailable p.left p.right Γ ((h:ℝ)+3/2) ∧
--         (∀ N, HasBorelProductPartition (Γ N) ((2:ℝ)^(2*((h+3:ℕ):ℝ)*ω*(N:ℝ))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.CapAvailable`, `OAI.Falconer.HasBorelProductPartition` and `OAI.Falconer.Space` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedFiniteLoomisWhitney` (definitions bundle `OAIQ088F001` of this split); `OAI.Falconer.PublishedHeavyHyperplanes`, `OAI.Falconer.PublishedPlanarFurstenberg`, `OAI.Falconer.PublishedRadialMoment`, `OAI.Falconer.TwoProjectionFrame`, `OAI.Falconer.TwoProjectionPieces`, `OAI.Falconer.supportPair`, `OAI.Falconer.TwoProjectionPieces.left` and `OAI.Falconer.TwoProjectionPieces.right` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.prepared_pair_of_lower_dimensions` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Angular/OddOriginalCaps.lean (declaration OAI.Falconer.TwoProjectionPieces.odd_original_caps_partition)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {μ : ProbabilityMeasure (Space d)} {α ε : ℝ}
  {f : TwoProjectionFrame μ (h+3) (h+2) α}

namespace TwoProjectionPieces

theorem odd_original_caps_partition (p : TwoProjectionPieces f ε)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    (hα : (h:ℝ)+3/2 < α) (hα' : α < (h:ℝ)+2)
    {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ Γ : ℕ → Set (Space d × Space d),
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < ((p.left : Measure (Space d)).prod (p.right : Measure (Space d))) (⋂ N, Γ N) ∧
      (∀ N, Γ N ⊆ supportPair p.left p.right) ∧
      CapAvailable p.left p.right Γ ((h:ℝ)+3/2) ∧
      (∀ N, HasBorelProductPartition (Γ N) ((2:ℝ)^(2*((h+3:ℕ):ℝ)*ω*(N:ℝ)))) := by
  sorry

end TwoProjectionPieces
end Falconer

end OAI
end
