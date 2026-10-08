-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondII_eq_39
-- name    : NonuniformKuramoto.CondII.eq_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:56.69317+00:00
-- url     : https://prove2.me/theorems/1ce99bd8-63db-4785-9c63-d411841374bd
-- title:
--   (39), p. 26 — min{D_iD_j}‖Hθ‖₂² ≤ 2W(Hθ) ≤ max{D_iD_j}‖Hθ‖₂²
-- statement:
--   Let $n\ge2$ and $D_1,\dots,D_n>0$. For every configuration $\theta$, the Lyapunov function $W(H\theta)=\tfrac12\sum_{i<j}D_iD_j(\theta_i-\theta_j)^2$ of (34) satisfies
--   $$
--   \min_{i\ne j}\{D_iD_j\}\,\|H\theta\|_2^2\ \le\ 2\cdot W(H\theta)\ \le\ \max_{i\ne j}\{D_iD_j\}\,\|H\theta\|_2^2 .\tag{39}
--   $$
--
--   These sandwich bounds let sublevel sets of $W$ be fitted between balls of $\|H\theta\|_2$, with ratio of radii $\alpha$.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 26, (39)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace NonuniformKuramoto.CondII

/-- Inequality (39) (Dörfler–Bullo, arXiv:0910.5673v4, p. 26):
`min_{i≠j}{D_iD_j} ‖Hθ‖₂² ≤ 2 W(Hθ) ≤ max_{i≠j}{D_iD_j} ‖Hθ‖₂²`. -/
theorem eq_39 {n : ℕ} (D : Fin n → ℝ) (hn : 2 ≤ n) (hD : ∀ i, 0 < D i) (θ : Fin n → ℝ) :
    minDD D * normH θ ^ 2 ≤ 2 * W D θ ∧ 2 * W D θ ≤ maxDD D * normH θ ^ 2 := by sorry

end NonuniformKuramoto.CondII
