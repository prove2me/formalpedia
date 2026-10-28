-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_CircleSigns_disk_family_finrank_le_two
-- name    : OAI.StrictHotSpots.CircleSigns.disk_family_finrank_le_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:00:28.63+00:00
-- url     : https://prove2.me/theorems/e4d52e3b-e0aa-4691-8bc2-f72e6e16369a
-- title:
--   OAI.StrictHotSpots.CircleSigns.disk_family_finrank_le_two: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.CircleSigns.disk_family_finrank_le_two` of [lean/OAI/Analysis/HotSpots/HotSpots/Multiplicity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplicity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.CircleSigns`, with `open Set MeasureTheory Metric Function Module`, `open scoped Topology InnerProductSpace`):
--
--   ```lean
--   theorem disk_family_finrank_le_two (F : ℂ → E)
--       (hc : ContinuousOn F (closedBall 0 1))
--       (hb : ∀ a : E, a ≠ 0 → ∃ s : Circle, 0 < inner ℝ a (F s))
--       (hp : ∀ a : E, a ≠ 0 → IsConnected
--         (ball (0:ℂ) 1 ∩ {z | 0 < inner ℝ a (F z)}))
--       (hn : ∀ a : E, a ≠ 0 → IsConnected
--         (ball (0:ℂ) 1 ∩ {z | inner ℝ a (F z) < 0})) : finrank ℝ E ≤ 2
--   ```
--
--   **Used by.** The proof of `OAI.StrictHotSpots.closedTraceSpace_rank` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Multiplicity.lean (declaration OAI.StrictHotSpots.CircleSigns.disk_family_finrank_le_two)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section MultiplicityComplete

noncomputable section

section DiskMultiplicityLayer
open Set MeasureTheory Metric Function Module
open scoped Topology InnerProductSpace
namespace StrictHotSpots.CircleSigns
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem disk_family_finrank_le_two (F : ℂ → E)
    (hc : ContinuousOn F (closedBall 0 1))
    (hb : ∀ a : E, a ≠ 0 → ∃ s : Circle, 0 < inner ℝ a (F s))
    (hp : ∀ a : E, a ≠ 0 → IsConnected
      (ball (0:ℂ) 1 ∩ {z | 0 < inner ℝ a (F z)}))
    (hn : ∀ a : E, a ≠ 0 → IsConnected
      (ball (0:ℂ) 1 ∩ {z | inner ℝ a (F z) < 0})) : finrank ℝ E ≤ 2 := by
  sorry
end StrictHotSpots.CircleSigns
end DiskMultiplicityLayer
end
end MultiplicityComplete

end OAI
end
