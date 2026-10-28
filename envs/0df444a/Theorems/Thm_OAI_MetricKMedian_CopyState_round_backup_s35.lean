-- Prove2me | Theorems.Thm_OAI_MetricKMedian_CopyState_round_backup_s35
-- name    : OAI.MetricKMedian.CopyState.round_backup_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:35:17.248979+00:00
-- url     : https://prove2.me/theorems/95ef6178-2866-453e-a30d-f580eaa7ce86
-- title:
--   OAI.MetricKMedian.CopyState.round_backup_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.CopyState`, with `open Finset PhysicalPotential FixedBatch`):
--
--   ```lean
--   theorem round_backup_s35 (A S₀ : Finset (Copy (F := F) Δ))
--       (location : F → X) (client : X) {g P R : ℝ}
--       (D : Taper.GraphData Δ g P (fun i : A => location i.val.1) (own Δ A))
--       (G : A → Finset A) (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
--       (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P ≤ 1/2) (hR : 0 ≤ R)
--       (hm : mass g S₀=1) (hd : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
--       (hgood : D.Good G)
--       (hbackup : (¬∃ f ∈ integral Δ A, dist client (location f) ≤ 5*R) → S₀ ⊆ A) :
--       (¬∃ f ∈ integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)),
--         dist client (location f) ≤ 5*R) →
--         S₀ ⊆ next Δ A (roundErased A G H Z) (roundOpened A G H Z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy`, `OAI.MetricKMedian.CopyState.integral`, `OAI.MetricKMedian.CopyState.own` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FixedBatch.HeavyAction` and `OAI.MetricKMedian.FixedBatch.graphActions` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.Taper.GraphData` and `OAI.MetricKMedian.Taper.GraphData.Good` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.CopyState.next` and `OAI.MetricKMedian.CopyState.roundErased` (definitions bundle `OAIQ035K015` of this split); `OAI.MetricKMedian.CopyState.roundOpened` (definitions bundle `OAIQ035K016` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F X : Type*} [Fintype F] [DecidableEq F] [PseudoMetricSpace X] {Δ : ℕ}

theorem round_backup_s35 (A S₀ : Finset (Copy (F := F) Δ))
    (location : F → X) (client : X) {g P R : ℝ}
    (D : Taper.GraphData Δ g P (fun i : A => location i.val.1) (own Δ A))
    (G : A → Finset A) (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H))
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P ≤ 1/2) (hR : 0 ≤ R)
    (hm : mass g S₀=1) (hd : ∀ i ∈ S₀, dist client (location i.1) ≤ R)
    (hgood : D.Good G)
    (hbackup : (¬∃ f ∈ integral Δ A, dist client (location f) ≤ 5*R) → S₀ ⊆ A) :
    (¬∃ f ∈ integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)),
      dist client (location f) ≤ 5*R) →
      S₀ ⊆ next Δ A (roundErased A G H Z) (roundOpened A G H Z) := by
  sorry

end MetricKMedian.CopyState
end
end

end OAI
end
