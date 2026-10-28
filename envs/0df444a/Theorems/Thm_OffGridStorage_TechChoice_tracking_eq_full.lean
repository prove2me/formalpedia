-- Prove2me | Theorems.Thm_OffGridStorage_TechChoice_tracking_eq_full
-- name    : OffGridStorage.TechChoice.tracking_eq_full
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:49.10714+00:00
-- url     : https://prove2.me/theorems/9291ab6b-c9cf-44ea-a01b-5af076fe569b
-- title:
--   A.4.3, eq. (30), p. 40 — for K ≤ D_L the tracking and full-discharge profits coincide
-- statement:
--   Under the standing assumptions, for every plan with $Q\ge 0$ and $0\le K\le D_L$,
--
--   $$\Pi_{TR}(Q,K)=\Pi_F(Q,K).$$
--
--   When the storage capacity does not exceed the nightly demand, all stored energy is used up each night, so no charge carries over ($x_t=0$ for every $t$) and each period of the tracking model behaves like an independent copy of the full-discharge model.
--
--   This identity is what lets the paper study the tracking model's investment threshold through the tractable full-discharge model.
--
--   **Formalization Note** Both sides carry the factor $T$ (eq. (4) and eq. (5)); the display (30) on p. 40 is written per period.
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), p. 40, Appendix A.4.3, eq. (30)

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

namespace OffGridStorage.TechChoice

/-- A.4.3, eq. (30), p. 40: for `K ≤ D_L` the tracking and full-discharge profits coincide. -/
theorem tracking_eq_full (p : Params) (hp : Standing p) (Q K : ℝ) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hKL : K ≤ p.DL) :
    profitTR p Q K = profitF p Q K := by sorry

end OffGridStorage.TechChoice
