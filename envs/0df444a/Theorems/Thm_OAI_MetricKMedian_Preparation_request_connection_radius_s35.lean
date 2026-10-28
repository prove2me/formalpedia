-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_request_connection_radius_s35
-- name    : OAI.MetricKMedian.Preparation.request_connection_radius_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:37:33.447273+00:00
-- url     : https://prove2.me/theorems/709e4d40-13b4-41fb-b549-f00c273bc8a9
-- title:
--   OAI.MetricKMedian.Preparation.request_connection_radius_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation`, with `open Finset SupplierStars`):
--
--   ```lean
--   theorem request_connection_radius_s35 (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
--       (V : T → ℝ) {M δ γ β : ℝ} (G : BundleGeometry F y s i V M δ)
--       (hy : ∀ a, 0 ≤ y a) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) (hsep : β+δ < 1)
--       (j : X) (t : T) (hD : 0 < G.c t → dist j (s t) ≤ β*G.L t)
--       (q : Star I T → ℝ) (htarget : ∀ e, t ∉ targets G.A e → q e=0)
--       (hzero : ∀ e, weight y G.P G.A G.c γ e=0 → q e=0) :
--       ∀ e, 0 < q e → match supplier G.next e with
--         | .inl a => dist j (i a) ≤ connectionCharge G.P G.A y (fun a => dist j (i a)) G.L
--             (1+2*δ/(1-β-δ)) β δ e
--         | .inr u => ∀ a ∈ G.P u, dist j (i a) ≤
--             connectionCharge G.P G.A y (fun a => dist j (i a)) G.L (1+2*δ/(1-β-δ)) β δ e
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Preparation.BundleGeometry`, `OAI.MetricKMedian.Preparation.SupplierStars.Star`, `OAI.MetricKMedian.Preparation.SupplierStars.targets` and `OAI.MetricKMedian.Preparation.SupplierStars.weight` (definitions bundle `OAIQ035K010` of this split); `OAI.MetricKMedian.Preparation.SupplierStars.connectionCharge` and `OAI.MetricKMedian.Preparation.SupplierStars.supplier` (definitions bundle `OAIQ035K025` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.distant_assignments_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K025

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem request_connection_radius_s35 (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ γ β : ℝ} (G : BundleGeometry F y s i V M δ)
    (hy : ∀ a, 0 ≤ y a) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) (hsep : β+δ < 1)
    (j : X) (t : T) (hD : 0 < G.c t → dist j (s t) ≤ β*G.L t)
    (q : Star I T → ℝ) (htarget : ∀ e, t ∉ targets G.A e → q e=0)
    (hzero : ∀ e, weight y G.P G.A G.c γ e=0 → q e=0) :
    ∀ e, 0 < q e → match supplier G.next e with
      | .inl a => dist j (i a) ≤ connectionCharge G.P G.A y (fun a => dist j (i a)) G.L
          (1+2*δ/(1-β-δ)) β δ e
      | .inr u => ∀ a ∈ G.P u, dist j (i a) ≤
          connectionCharge G.P G.A y (fun a => dist j (i a)) G.L (1+2*δ/(1-β-δ)) β δ e := by
  sorry

end MetricKMedian.Preparation
end
end

end OAI
end
