-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_PolytopeCertificate_approximate_implies_feasible_s238
-- name    : OAI.MetricKMedianRecovery.PolytopeCertificate.approximate_implies_feasible_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:15:26.55754+00:00
-- url     : https://prove2.me/theorems/e17aa852-3233-45aa-9828-b34b51e8c6cc
-- title:
--   OAI.MetricKMedianRecovery.PolytopeCertificate.approximate_implies_feasible_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.PolytopeCertificate.approximate_implies_feasible` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/BoundedMinimizingExtreme.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BoundedMinimizingExtreme.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.PolytopeCertificate`, with `open Matrix`, `open scoped BigOperators`):
--
--   ```lean
--   theorem approximate_implies_feasible_s238 (A : Matrix R V ℤ) (b : R → ℤ) (B H : ℤ)
--       (hB : 0 ≤ B) (hH : 1 ≤ H) (hA : ∀ r j, |A r j|≤H) (hb : ∀ r, |b r|≤H)
--       (eps : ℝ) (heps0 : 0≤eps) (hepsH : eps≤(H:ℝ))
--       (heps : eps < 1 / ((Fintype.card (Option V)).factorial *
--         ((Fintype.card (SlackRow R V):ℤ)*(max H B)^2)^(Fintype.card (Option V)) : ℤ))
--       (x : V → ℝ) (hx : ∀ j, -(B:ℝ)≤x j ∧ x j≤(B:ℝ))
--       (ha : ∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)+eps) :
--       ∃ y ∈ region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ)),
--         ∀ j, -(B:ℝ)≤y j ∧ y j≤(B:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.PolytopeCertificate.SlackRow` and `OAI.MetricKMedianRecovery.PolytopeCertificate.region` (definitions bundle `Q238K004` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BoundedMinimizingExtreme.lean (declaration OAI.MetricKMedianRecovery.PolytopeCertificate.approximate_implies_feasible)

import Mathlib
import Definitions.Def_Q238K004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PolytopeCertificate

open Matrix
open scoped BigOperators
variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

theorem approximate_implies_feasible_s238 (A : Matrix R V ℤ) (b : R → ℤ) (B H : ℤ)
    (hB : 0 ≤ B) (hH : 1 ≤ H) (hA : ∀ r j, |A r j|≤H) (hb : ∀ r, |b r|≤H)
    (eps : ℝ) (heps0 : 0≤eps) (hepsH : eps≤(H:ℝ))
    (heps : eps < 1 / ((Fintype.card (Option V)).factorial *
      ((Fintype.card (SlackRow R V):ℤ)*(max H B)^2)^(Fintype.card (Option V)) : ℤ))
    (x : V → ℝ) (hx : ∀ j, -(B:ℝ)≤x j ∧ x j≤(B:ℝ))
    (ha : ∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)+eps) :
    ∃ y ∈ region (fun r j => (A r j:ℝ)) (fun r => (b r:ℝ)),
      ∀ j, -(B:ℝ)≤y j ∧ y j≤(B:ℝ) := by
  sorry

end MetricKMedianRecovery.PolytopeCertificate

end OAI
end
