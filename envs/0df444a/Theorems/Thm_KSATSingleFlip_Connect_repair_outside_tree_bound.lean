-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_outside_tree_bound
-- name    : KSATSingleFlip.Connect.repair_outside_tree_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:56:53.704203+00:00
-- url     : https://prove2.me/theorems/fab1902e-78c5-4449-9f3f-03ca4294de15
-- title:
--   Variables outside retained Repair trees
-- statement:
--   Let $s$ be any state reachable by Repair, let $U$ be its current repair-variable set, let $V(F)$ be the union of variables in the currently retained trees, let $J$ be its matching-assigned clause set, and let $W$ be the initial variable set. If $\log k\ge1$, then
--
--   $$|U\setminus V(F)|\le |W|+4(\log k)^6|J|.$$
--
--   The bound holds for every choice allowed by the Repair relation. It is the outside-tree charging estimate used in the proof of Lemma 7.12; it does not by itself bound all of $U$.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf, proof of Lemma 7.12, printed p. 64 (PDF p. 66).

import Definitions.Def_KSATSingleFlip_Connect_Repair

namespace KSATSingleFlip.Connect

/-- The variables outside retained trees are controlled by the initial set and matching clauses. -/
theorem repair_outside_tree_bound {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ) (hlog : 1 ≤ Real.log k)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    ((s.U \ s.VF).card : ℝ) ≤ W.card + 4 * Real.log k ^ 6 * s.J.card := by sorry

end KSATSingleFlip.Connect
