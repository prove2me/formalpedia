-- Prove2me | Theorems.Thm_GTWSched_MaxDisc_corollary_1
-- name    : GTWSched.MaxDisc.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:49:54.904907+00:00
-- url     : https://prove2.me/theorems/ae6080ef-101c-4350-b8f6-a70ec7cc6ca2
-- title:
--   COROLLARY 1, p. 344 — some optimum schedule executes before T_N exactly the tasks with deadline ≤ β
-- statement:
--   Let $N$ tasks have lengths $l_i \ge 0$, release times $r_i \ge 0$ and deadlines $d_i$ in special form for $\alpha \ge 0$, and let $T_n$ be a task of maximum deadline. If a feasible schedule exists, then there are an optimum schedule and a real number $\beta \ge 0$ such that for every task $T_i \ne T_n$,
--
--   $$T_i \text{ is executed before } T_n \iff d_i \le \beta.$$
--
--   This is the form of Theorem 4 on which the paper's algorithm is built: the set of tasks before the maximum-deadline task is a deadline threshold set.
--
--   **Formalization Note.** The paper says "the set of tasks executed before $T_N$ is exactly the set of all tasks with deadline $\beta$ or less". The set is read as excluding $T_N$ itself: in the proof $\beta = t + \alpha$ with $t$ the start of $T_N$, and $d_N \le t + \alpha$ may hold, in which case $T_N$ would belong to the set of tasks with deadline at most $\beta$ although it is not executed before itself. This is the only reading under which the corollary holds.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 344, COROLLARY 1

import Mathlib
import Definitions.Def_GTWSched_MaxDisc_Model

namespace GTWSched.MaxDisc

theorem corollary_1 {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (hn : ∀ i, d i ≤ d n)
    (hfeas : ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ), Feasible r d l σ s) :
    ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) (β : ℝ),
      Optimum r d l σ s ∧ 0 ≤ β ∧
        ∀ i, i ≠ n → (σ.symm i < σ.symm n ↔ d i ≤ β) := by sorry

end GTWSched.MaxDisc
