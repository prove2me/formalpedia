-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_set_bound_7_4
-- name    : KSATSingleFlip.Connect.repair_set_bound_7_4
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:06:47.813388+00:00
-- url     : https://prove2.me/theorems/905fd3b6-713b-4cfd-a110-2cf0cedaa74b
-- title:
--   Repair-set size bound, equation (7.4)
-- statement:
--   Let $U$ be the repair-variable set at a state reachable by Repair, and let $W$ be the initial variable set. Assume $k\ge4$, $\log k\ge2$, the initial assignment satisfies the designated subformula, the repair bounds hold, at most $\rho^4n$ omitted clauses are weak, $|U|\le\rho n$, and $1\le\rho^4n$. Then
--
--   $$|U|\le4(\log k)^{14}|W|+32(\log k)^{20}\rho^4n.$$
--
--   The explicit size hypotheses isolate the quantitative estimate (7.4); a separate first-crossing argument is needed to establish $|U|\le\rho n$ throughout the run.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf, equation (7.4), proof of Lemma 7.12, printed p. 65 (PDF p. 67).

import Definitions.Def_KSATSingleFlip_Connect_Repair

namespace KSATSingleFlip.Connect

/-- The repair-set bound displayed as equation (7.4) in the source. -/
theorem repair_set_bound_7_4 {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ) (hk : 4 ≤ k) (hlog : 2 ≤ Real.log k)
    (hx : x ∈ sols (subF Φ I0))
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hBounds : RepairBounds k Φ I0 x)
    (hD : ((omittedWeak Φ I0 x).card : ℝ) ≤ rho k ^ 4 * n)
    (hU : (s.U.card : ℝ) ≤ rho k * n)
    (hn : 1 ≤ rho k ^ 4 * n) :
    (s.U.card : ℝ) ≤ 4 * Real.log k ^ 14 * W.card +
      32 * Real.log k ^ 20 * rho k ^ 4 * n := by sorry

end KSATSingleFlip.Connect
