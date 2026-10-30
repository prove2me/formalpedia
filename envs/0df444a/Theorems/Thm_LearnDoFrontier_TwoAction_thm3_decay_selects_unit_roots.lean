-- Prove2me | Theorems.Thm_LearnDoFrontier_TwoAction_thm3_decay_selects_unit_roots
-- name    : LearnDoFrontier.TwoAction.thm3_decay_selects_unit_roots
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:47.080373+00:00
-- url     : https://prove2.me/theorems/073f9309-2597-4dc1-ac36-2fd91c93c2d9
-- title:
--   Proof of Theorem 3, EC p. 4 — decay v(∞) = 0 forces α_{z,τ} = 0 for every root with |z| ≥ 1
-- statement:
--   Let $z_1, \dots, z_r \in \mathbb C$ be distinct, $m_1, \dots, m_r \in \mathbb N$, and $b_{i,\tau} \in \mathbb C$ for $0 \le \tau \le m_i - 1$. If
--   $$\sum_{i=1}^r \Big(\sum_{\tau=0}^{m_i - 1} b_{i,\tau} k^\tau\Big) z_i^k \longrightarrow 0 \qquad (k \to \infty),$$
--   then $b_{i,\tau} = 0$ for every $i$ with $|z_i| \ge 1$ and every $\tau$.
--
--   In the proof of Theorem 3 this is the step "because $v^A_\theta(\infty) = 0$, we must have $\alpha_{z,\tau} = 0$ for all $|z| \ge 1$": the decay condition discards every characteristic root outside the open unit disk, including roots on the unit circle.
--
--   **Formalization Note** The expansion is the form (20) of the paper, $\sum_i \sum_\tau b_{i,\tau} k^\tau z_i^k$, with $0^0 = 1$.
-- source:
--   Zhang, SSRN 3847049 (accepted version with E-Companion), EC p. 4 (PDF p. 47), proof of Theorem 3; p. 21, Eq. (20)

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra

open Filter Topology

namespace LearnDoFrontier.TwoAction

theorem thm3_decay_selects_unit_roots {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (hz : Function.Injective z) (b : (Σ i : Fin r, Fin (m i)) → ℂ)
    (hdecay : Tendsto (fun k : ℕ => exp3 z m b k) atTop (𝓝 0)) :
    ∀ p : (Σ i : Fin r, Fin (m i)), 1 ≤ ‖z p.1‖ → b p = 0 := by sorry

end LearnDoFrontier.TwoAction
