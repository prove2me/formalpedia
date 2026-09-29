-- Prove2me | Theorems.Thm_NetworkControl_CapacityRegion_lemma_necessary_condition_strong_stability
-- name    : NetworkControl.CapacityRegion.lemma_necessary_condition_strong_stability
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-21T06:20:05.408991+00:00
-- url     : https://prove2.me/theorems/3b5b4cb3-694f-4c5a-852e-22c52dbe09d9
-- title:
--   Lemma 3.3 — necessary condition for strong stability
-- statement:
--   **Lemma 3.3** (p. 24). If a queue is strongly stable, and either $\mathbb E\{A(t)\}\le A_{\max}$
--   for all $t$, or $\mathbb E\{\mathrm{svc}(t)-A(t)\}\le D_{\max}$ for all $t$, where $A_{\max},
--   D_{\max}$ are finite nonnegative constants, then $\lim_{t\to\infty}\mathbb E\{U(t)\}/t=0$
--   (Eq. 3.1). Formalized directly on the real sequences `U`, `A`, `svc` representing
--   $\mathbb E\{U(t)\}$, $\mathbb E\{A(t)\}$, $\mathbb E\{\mathrm{svc}(t)\}$, which is exactly the
--   content the book's own statement and proof use — no further probabilistic structure enters.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 24, Lemma 3.3

import Mathlib
import Definitions.Def_NetworkControl_CapacityRegion_StronglyStable

namespace NetworkControl.CapacityRegion

/-- Lemma 3.3 (Necessary Condition for Strong Stability), p. 24. If a queue's expected backlog
sequence `U` is strongly stable, and either the expected arrivals `A` are uniformly bounded by
`Amax`, or the expected `svc - A` gap is uniformly bounded by `Dmax` (`Amax, Dmax ≥ 0` finite),
then `E{U(t)}/t → 0`. -/
theorem lemma_necessary_condition_strong_stability
    (U A svc : ℕ → ℝ) (Amax Dmax : ℝ) (hAmax : 0 ≤ Amax) (hDmax : 0 ≤ Dmax)
    (hstable : StronglyStable U)
    (hbound : (∀ t : ℕ, A t ≤ Amax) ∨ (∀ t : ℕ, svc t - A t ≤ Dmax)) :
    Filter.Tendsto (fun t : ℕ => U t / (t : ℝ)) Filter.atTop (nhds 0) := by sorry

end NetworkControl.CapacityRegion
