-- Prove2me | Theorems.Thm_FourierRankQLB_eq_39
-- name    : FourierRankQLB.eq_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:45:40.673466+00:00
-- url     : https://prove2.me/theorems/7f52f467-a7fa-449a-af0c-3e6de8d51c98
-- title:
--   Eq. (39) — the hard ellipsoids lie between two balls
-- statement:
--   Let $n\ge2$, $d=d_n$ and $s>0$. For every $Q\in O(d)$, the hard ellipsoid $K_{s,Q}=\{y: y^T\overline A_{n,Q}y\le s^2\}$ satisfies
--   $$
--   B_2(0,r_s)\subseteq K_{s,Q}\subseteq B_2(0,R_s),\qquad r_s=\frac{s}{\sqrt{1+2g_d}},\quad R_s=\frac{s}{\sqrt{2g_d}} .
--   $$
--
--   This places the hard family inside the standard oracle model (3), with radii that do not depend on $Q$.
--
--   Differences from the source:
--
--   - encoding: the ambient dimension $n$ of §4–5, with §5.1 fixing $n\ge2$ → hypothesis `2 ≤ n`; reason: the standing assumption; it excludes $d=0$, where $g_d$ and the radii degenerate
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (39), p.25

import Mathlib
import Definitions.Def_FourierRankQLB_hardBody
import Definitions.Def_FourierRankQLB_rs
import Definitions.Def_FourierRankQLB_Rs__d75a51

namespace FourierRankQLB

/-- Eq. (39): the hard ellipsoids lie between two balls, `B₂(0, r_s) ⊆ K_{s,Q} ⊆ B₂(0, R_s)`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (39), p. 25. -/
theorem eq_39 {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (Q : Od (dn n)) :
    Metric.closedBall (0 : Ambient n) (rs n s) ⊆ hardBody s Q ∧
      hardBody s Q ⊆ Metric.closedBall (0 : Ambient n) (Rs n s) := by sorry

end FourierRankQLB
