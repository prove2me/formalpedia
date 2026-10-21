-- Prove2me | Theorems.Thm_OffGridStorage_TechChoice_theorem_4_i
-- name    : OffGridStorage.TechChoice.theorem_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:53.671983+00:00
-- url     : https://prove2.me/theorems/caefad78-cfa7-4dc5-b262-c27b20148f9d
-- title:
--   Theorem 4, first bullet, p. 13 — if g ≤ g0, the plan (D_H√(g/2c_Q), 0) is optimal in both models and the profits coincide
-- statement:
--   Under the standing assumptions, suppose $g\le g_0=c_Q+c_K/e+\sqrt{c_Q^2+2c_Qc_K/e}$ and let $Q_0=D_H\sqrt{g/(2c_Q)}$. Then
--
--   1. $(Q_0,0)$ is an optimal plan of the full-discharge model;
--   2. $(Q_0,0)$ is an optimal plan of the tracking model;
--   3. $\Pi_{TR}(Q_0,0)=\Pi_F(Q_0,0)$, so the two optimal profits coincide.
--
--   Below the threshold $g_0$ the backup is too cheap for storage to pay, and the full-discharge approximation is exact.
--
--   **Formalization Note** The paper writes $K^*_F=K^*_{TR}=0$, $Q^*_F=Q^*_{TR}$ as if the optima were unique, and refers to "the decisions from Theorem 3". Two corrections are made. First, Theorem 3's printed $Q^*_F$ ignores the constraint $K\ge 0$ and is wrong when $K^*_F=0$; the correct no-storage optimum is $Q_0=D_H\sqrt{g/(2c_Q)}$ (eq. (25)). Second, uniqueness can fail: at $g=g_0$ with $e=1$ the closed form is linear along a ray from $(Q_0,0)$, so plans with $0<K\le D_L$ are optimal too. The statement therefore asserts that $(Q_0,0)$ is optimal in both models, and that the optimal values agree.
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), p. 13, Theorem 4, first bullet; proof Appendix A.4.1, pp. 38–39

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

namespace OffGridStorage.TechChoice

/-- Theorem 4, first bullet, p. 13 (restated): if `g ≤ g0`, the no-storage plan `(Q0, 0)`,
`Q0 = D_H √(g/(2c_Q))`, is optimal in both the full-discharge and the tracking model, and the two
profits coincide there. -/
theorem theorem_4_i (p : Params) (hp : Standing p) (hg : p.g ≤ g0 p) :
    IsOptimalF p (Q0 p) 0 ∧ IsOptimalTR p (Q0 p) 0 ∧
      profitTR p (Q0 p) 0 = profitF p (Q0 p) 0 := by sorry

end OffGridStorage.TechChoice
