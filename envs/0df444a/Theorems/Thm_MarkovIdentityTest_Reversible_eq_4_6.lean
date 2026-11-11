-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_eq_4_6
-- name    : MarkovIdentityTest.Reversible.eq_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:37:48.462636+00:00
-- url     : https://prove2.me/theorems/353798cf-1696-4243-8c60-02f7ccf6fbdf
-- title:
--   §4.3.3 Eq. (4.6) — the clipping identity $U_w(p;c)=U_v(q;c)+k(k-1)F+2(k-1)\kappa^\top(c-kq)+\sum_j(w_j-v_j)c_j(c_j-1)$
-- statement:
--   For weights $w$, vectors $p,q$ on $d$ coordinates and a count vector $c\in\mathbb N^d$ with total $k=\sum_jc_j$, let $v$ be the capped weights, $\kappa_j=v_jq_j-w_jp_j$ and $F=\sum_j(v_jq_j^2+w_jp_j^2-2w_jp_jq_j)$. Then
--   $$U_w(p;c)=U_v(q;c)+k(k-1)F+2(k-1)\kappa^\top(c-kq)+\sum_j(w_j-v_j)c_j(c_j-1).$$
--   The identity compares the statistic centred at the reference row with test weights to the statistic centred at the true row with capped weights; the second term is the row signal and the third the linear count error.
--
--   Differences from the source:
--
--   - generalization: one row: p, q probability vectors and w_j = 1/(p_j + τ) → arbitrary real vectors w, p, q; reason: the identity is pure algebra and specializes to the printed one
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 21, §4.3.3, Eq. (4.6)

import Mathlib
import Definitions.Def_MarkovIdentityTest_Reversible_RowStatistics

set_option autoImplicit false

namespace MarkovIdentityTest.Reversible

/-- §4.3.3, Eq. (4.6) (Jia, p. 21 / PDF 23): the clipping identity, for arbitrary real vectors
`w, p, q` and a count vector `c` with total `k`. -/
theorem eq_4_6 (d : ℕ) (w p q : Fin d → ℝ) (c : Fin d → ℕ) :
    pairStat w p c =
      pairStat (cappedWeight w q) q c
        + (∑ j, (c j : ℝ)) * ((∑ j, (c j : ℝ)) - 1) * rowSignal w p q
        + 2 * ((∑ j, (c j : ℝ)) - 1) *
            ∑ j, clipCoeff w p q j * ((c j : ℝ) - (∑ z, (c z : ℝ)) * q j)
        + ∑ j, (w j - cappedWeight w q j) * (c j : ℝ) * ((c j : ℝ) - 1) := by sorry

end MarkovIdentityTest.Reversible
