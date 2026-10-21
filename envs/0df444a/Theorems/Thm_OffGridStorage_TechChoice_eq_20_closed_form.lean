-- Prove2me | Theorems.Thm_OffGridStorage_TechChoice_eq_20_closed_form
-- name    : OffGridStorage.TechChoice.eq_20_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:49.202695+00:00
-- url     : https://prove2.me/theorems/e3cb6a59-cc68-45e6-94b6-a794a858071d
-- title:
--   Eq. (20), p. 37 — closed form of the full-discharge profit on D_H + K/e ≤ Q
-- statement:
--   Under the standing assumptions, for every $K\ge 0$ and $Q\ge D_H+K/e$,
--
--   $$\Pi_F(Q,K)=T\Bigl(\frac{g}{Q}\Bigl[-\frac{D_H^2}{2}-\frac{K^2}{2e}-KD_H\Bigr]+g(D_H+K)-\frac{c_K}{e}K-c_QQ\Bigr).$$
--
--   The bracketed term comes from evaluating the expected served energy $E[\min[q,D_H]+\min[e(q-D_H)^+,K]]$ for $q\sim U[0,Q]$, split as in eq. (30). The closed form is the basis of the paper's first-order analysis of the full-discharge model (Theorem 3, eq. (25)).
--
--   **Formalization Note** Eq. (20) is stated per period; $\Pi_F$ in eq. (5) carries the factor $T$, so the identity is stated with $T$. The region $Q\ge D_H+K/e$ is where the formula is valid (the storage term saturates within $[0,Q]$); the paper leaves it implicit.
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), p. 37, Appendix A.3, eq. (20); integrals of eq. (30), p. 40

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

namespace OffGridStorage.TechChoice

/-- Eq. (20), p. 37 (with eq. (30), p. 40): on the region `D_H + K/e ≤ Q` the full-discharge
profit equals `T` times the per-period closed form. -/
theorem eq_20_closed_form (p : Params) (hp : Standing p) (Q K : ℝ) (hK : 0 ≤ K)
    (hQK : p.DH + K / p.e ≤ Q) :
    profitF p Q K = closedFormF p Q K := by sorry

end OffGridStorage.TechChoice
