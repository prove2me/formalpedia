-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_repair_terminates
-- name    : KSATSingleFlip.Connect.repair_terminates
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:22:18.990196+00:00
-- url     : https://prove2.me/theorems/d6eade40-b708-42e0-bb4f-0f5cbe7bbd6a
-- title:
--   Repair admits a completed run
-- statement:
--   Let $\Phi$ be a finite Boolean formula on $n$ variables, let $I_0$ be a set of its clause positions, let $x$ be an assignment, let $W$ be a set of variables, and let $k$ be a natural number. Algorithm 3, initialized with these inputs, has a completed run:
--
--   $$\exists r,i\quad \operatorname{RepairRun}(k,\Phi,I_0,x,\operatorname{init}(\Phi,x,W),r,i).$$
--
--   The result $r$ may be a repaired assignment or failure. This termination statement is a supporting part of the repair analysis; it does not assert successful repair. The formal statement permits arbitrary finite clauses and assignments.
-- source:
--   Wang, Yin, Yu, and Zhang, Single-Variable Connectivity in Random k-SAT, https://arxiv.org/abs/2611.05981, Algorithm 3 and proof of Lemma 7.4, pp. 60–62; derived supporting statement.

import Definitions.Def_KSATSingleFlip_Connect_Repair

namespace KSATSingleFlip.Connect

/-- Algorithm 3 admits a completed run from its initial state. -/
theorem repair_terminates {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n)) :
    ∃ r i, RepairRun k Φ I0 x (RState.init Φ x W) r i := by sorry

end KSATSingleFlip.Connect
