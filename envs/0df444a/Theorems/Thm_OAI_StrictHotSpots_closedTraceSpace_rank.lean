-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_closedTraceSpace_rank
-- name    : OAI.StrictHotSpots.closedTraceSpace_rank
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:18:47.226976+00:00
-- url     : https://prove2.me/theorems/b4725a48-feaf-44c6-b1bf-bfe6e6e01488
-- title:
--   OAI.StrictHotSpots.closedTraceSpace_rank: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.closedTraceSpace_rank` of [lean/OAI/Analysis/HotSpots/HotSpots/TraceRank.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/TraceRank.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots`, with `open Set Function Module`, `open scoped Topology`, `open HilbertMultipliers`):
--
--   ```lean
--   lemma closedTraceSpace_rank {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
--       (hΩ : AdmissibleDomain Ω) : Module.Finite ℝ (closedTraceSpace c hΩ) ∧
--         finrank ℝ (closedTraceSpace c hΩ) ≤ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.Conformal.ClosedDiskChart` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.closedTraceSpace` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.AdmissibleDomain` and `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/TraceRank.lean (declaration OAI.StrictHotSpots.closedTraceSpace_rank)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedTraceRank

noncomputable section
open Set Function Module
open scoped Topology
namespace StrictHotSpots
open HilbertMultipliers

lemma closedTraceSpace_rank {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) : Module.Finite ℝ (closedTraceSpace c hΩ) ∧
      finrank ℝ (closedTraceSpace c hΩ) ≤ 2 := by
  sorry

end StrictHotSpots
end
end ClosedTraceRank

end OAI
end
