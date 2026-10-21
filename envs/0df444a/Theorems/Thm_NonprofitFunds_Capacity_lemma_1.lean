-- Prove2me | Theorems.Thm_NonprofitFunds_Capacity_lemma_1
-- name    : NonprofitFunds.Capacity.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:01.27686+00:00
-- url     : https://prove2.me/theorems/d2fcc5c6-4c90-4906-a5c0-014043352994
-- title:
--   Lemma 1, p. 12 (PDF 12) — the two-period problem (1) has the same optimal value as problem (2)
-- statement:
--   Fix the data and an admissible first-period capacity $k_1$ ($k_1\ge 0$, $B_1\ge 2m(k_1)$). Problem (1) at $t=1$ maximizes
--   $$(r+1)p_1+\mathbb E\big[V_2(B_2,\Psi,k_1+\delta(a_1))\big]$$
--   over $p_1,a_1,f_1\ge 0$ subject to (1a) $p_1+a_1+m(k_1)+f_1\le B_1$, (1b) $(r+1)p_1\le\min(k_1,\psi_1)$, (1c) $B_2=B_1-p_1-a_1-m(k_1)-f_1+D(p_1,a_1,f_1)$ and (1e) $B_2\ge m(k_1+\delta(a_1))$. Problem (2) maximizes
--   $$(r+1)p_1+\mathbb E_\Psi\big[\min\big(\Psi,(r+1)\hat B_2\big)\big],\qquad \hat B_2=D(p_1,a_1,f_1)-m(k_1+\delta(a_1)),$$
--   over $p_1,a_1,f_1\ge 0$ subject to (2a) $p_1+a_1+f_1=\hat B_1$, (2b) $(r+1)p_1\le\theta$, (2e) $\hat B_2\ge 0$ and (2f) $(r+1)\hat B_2\le k_1+\delta(a_1)$.
--
--   Lemma 1: both problems attain their maxima, and the maxima are equal, so problem (1) can be restated as problem (2).
--
--   The restated problem builds in the three remarks of §3.2: the whole net budget is spent (Remark 1), program spending is capped by $\theta/(r+1)$ (Remark 2), and the second-period budget never exceeds what the second-period capacity can use (Remark 3). All later results are statements about problem (2).
--
--   **Formalization Note.** "Restated" is formalized as: there is a number $v$ that is the greatest value of both problems. $V_2$ is the supremum defining the second-period value (Lemma S.1 gives its closed form).
-- source:
--   Kotsi, Aflaki, Aydin & Pedraza-Martinez, Allocation of nonprofit funds among program, fundraising, and administration, SSRN 3460795 (blinded MSOM submission), p. 12 (PDF 12), Lemma 1, problem (2a)–(2f); proof pp. S11–S12 (PDF 40–41)

import Mathlib
import Definitions.Def_NonprofitFunds_Capacity_Model

namespace NonprofitFunds.Capacity

/-- Lemma 1, p. 12: for every admissible first-period capacity, problem (1) at `t = 1` and
problem (2) attain the same optimal value. -/
theorem lemma_1 (P : Params) (hP : P.Standing) (k1 : ℝ) (hk1 : P.Admissible k1) :
    ∃ v : ℝ, IsGreatest (P.Val1 k1) v ∧ IsGreatest (P.Val2 k1) v := by sorry

end NonprofitFunds.Capacity
