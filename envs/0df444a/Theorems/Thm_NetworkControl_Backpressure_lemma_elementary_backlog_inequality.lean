-- Prove2me | Theorems.Thm_NetworkControl_Backpressure_lemma_elementary_backlog_inequality
-- name    : NetworkControl.Backpressure.lemma_elementary_backlog_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T06:21:52.298553+00:00
-- url     : https://prove2.me/theorems/2460cf44-ba24-4e9e-9bb2-5b90a02e85aa
-- title:
--   Lemma 4.3 — elementary per-slot backlog inequality
-- statement:
--   **Lemma 4.3** (p. 52, unnamed). If $V,U,\mu,A$ are nonnegative reals and $V\le\max[U-\mu,0]+A$,
--   then $V^2\le U^2+\mu^2+A^2-2U(\mu-A)$. A pure real-inequality lemma (no probability, no
--   queueing) used to bound the per-slot change in a single queue's squared backlog.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 52, Lemma 4.3 (unnamed)

import Mathlib

namespace NetworkControl.Backpressure

/-- Lemma 4.3 (unnamed elementary inequality), p. 52. If `V, U, μ, A` are nonnegative reals and
`V ≤ max[U-μ,0] + A`, then `V² ≤ U² + μ² + A² - 2U(μ-A)`. A pure real-inequality lemma (no
probability, no queueing) used to bound the per-slot change in a single queue's squared backlog. -/
theorem lemma_elementary_backlog_inequality
    (V U μ A : ℝ) (hV : 0 ≤ V) (hU : 0 ≤ U) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (h : V ≤ max (U - μ) 0 + A) :
    V ^ 2 ≤ U ^ 2 + μ ^ 2 + A ^ 2 - 2 * U * (μ - A) := by sorry

end NetworkControl.Backpressure
