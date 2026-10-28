-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Reduction_CloseCenters_complete_of_choices_s35
-- name    : OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:37:55.213023+00:00
-- url     : https://prove2.me/theorems/1fe55eee-5598-4500-a4ba-94b64218efc2
-- title:
--   OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Reduction.CloseCenters`, with `open Finset`):
--
--   ```lean
--   theorem complete_of_choices_s35 (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
--       (hO : O.Nonempty) (F : Finset (Fin I.n)) (hOF : O ⊆ F)
--       (a : ↥G → Fin I.n) (ha : ∀ t, a t ∈ F) (hclose : ∀ t, dist t.val (a t) ≤ δ*C.radius t)
--       (hloc : ∀ t, (∑ j ∈ C.region t, nearest I j (insert (a t) C.backup)) ≤
--         ∑ j ∈ C.region t, nearest I j (insert (C.matchTo t) C.backup)) :
--       let S := C.backup ∪ univ.image a
--       S ⊆ F ∧ S.Nonempty ∧ S.card ≤ O.card ∧ cost I S ≤ (1+12*δ)*cost I O
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Reduction.CloseCenters`, `OAI.MetricKMedian.Reduction.CloseCenters.backup` and `OAI.MetricKMedian.Reduction.CloseCenters.region` (definitions bundle `OAIQ035K025` of this split); `OAI.MetricKMedian.Reduction.instPseudoMetricSpaceFinN` (definitions bundle `OAIQ035K026` of this split); `OAI.MetricKMedian.Instance`, `OAI.MetricKMedian.cost` and `OAI.MetricKMedian.nearest` (the published bundle `Def_MetricKMedian`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K025
import Definitions.Def_OAIQ035K026

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

namespace CloseCenters
variable {G O : Finset (Fin I.n)} {δ : ℝ}

attribute [local instance] OAI.MetricKMedian.Reduction.instPseudoMetricSpaceFinN
theorem complete_of_choices_s35 (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
    (hO : O.Nonempty) (F : Finset (Fin I.n)) (hOF : O ⊆ F)
    (a : ↥G → Fin I.n) (ha : ∀ t, a t ∈ F) (hclose : ∀ t, dist t.val (a t) ≤ δ*C.radius t)
    (hloc : ∀ t, (∑ j ∈ C.region t, nearest I j (insert (a t) C.backup)) ≤
      ∑ j ∈ C.region t, nearest I j (insert (C.matchTo t) C.backup)) :
    let S := C.backup ∪ univ.image a
    S ⊆ F ∧ S.Nonempty ∧ S.card ≤ O.card ∧ cost I S ≤ (1+12*δ)*cost I O := by
  sorry

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
end
