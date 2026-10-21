-- Prove2me | Theorems.Thm_OffGridStorage_TechChoice_tracking_le_full
-- name    : OffGridStorage.TechChoice.tracking_le_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:47.917792+00:00
-- url     : https://prove2.me/theorems/43bc380f-077f-4ff6-9615-04abfadc6b4c
-- title:
--   A.4.3, p. 40 — the full-discharge profit dominates the tracking profit: Π_TR(Q,K) ≤ Π_F(Q,K)
-- statement:
--   Under the standing assumptions, for every plan $Q\ge 0$, $K\ge 0$,
--
--   $$\Pi_{TR}(Q,K)\le \Pi_F(Q,K).$$
--
--   The full-discharge model assumes that every unit charged in a period is discharged profitably within the period, whereas the tracking model serves only actual demand and carries charge over; the full-discharge profit therefore over-values storage. The paper uses this comparison in the proof of Theorem 4 (A.4.3).
--
--   **Formalization Note** The paper states the comparison for $K>D_L$ ("the profit is trivially larger in the full-discharge case"); for $K\le D_L$ the two profits are equal (the companion milestone). The Lean statement is the weak inequality for all $K\ge 0$, which covers both cases; a strict inequality is false in general (for instance when $Q\le D_H$ nothing is ever charged).
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), p. 40, Appendix A.4.3 (Part 3 of the proof of Theorem 4)

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

namespace OffGridStorage.TechChoice

/-- A.4.3, p. 40: the full-discharge profit is never below the tracking profit. -/
theorem tracking_le_full (p : Params) (hp : Standing p) (Q K : ℝ) (hQ : 0 ≤ Q) (hK : 0 ≤ K) :
    profitTR p Q K ≤ profitF p Q K := by sorry

end OffGridStorage.TechChoice
