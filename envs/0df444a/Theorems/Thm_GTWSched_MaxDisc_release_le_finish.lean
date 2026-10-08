-- Prove2me | Theorems.Thm_GTWSched_MaxDisc_release_le_finish
-- name    : GTWSched.MaxDisc.release_le_finish
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:50:11.833862+00:00
-- url     : https://prove2.me/theorems/4626c235-16d3-4b91-9cb6-639ac4fc64e3
-- title:
--   §3.1, p. 344 — every task after T_N is released by the time T_N finishes
-- statement:
--   Let $N$ tasks have lengths $l_i \ge 0$, release times $r_i \ge 0$ and deadlines $d_i$ in special form for $\alpha \ge 0$, and let $T_n$ be a task of maximum deadline. In every feasible schedule, every task $T_i$ executed after $T_n$ satisfies
--
--   $$r_i \le s_n + l_n,$$
--
--   i.e. it is released no later than the time at which $T_n$ finishes.
--
--   The paper derives from this that there is no need for idle time after $T_N$ starts and that the tasks after $T_N$ can be taken in nondecreasing order of deadlines; both steps lead to the standard form.
--
--   **Formalization Note.** The paper states this for optimum schedules of the form given by Corollary 1. The statement here holds for every feasible schedule, since the argument uses only the special form, the maximality of $d_n$ and $r_n \le s_n$.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 344, paragraph after the proof of COROLLARY 1 ("In particular, this says that all tasks executed after T_N must have release times no greater than the time at which T_N finishes")

import Mathlib
import Definitions.Def_GTWSched_MaxDisc_Model

namespace GTWSched.MaxDisc

theorem release_le_finish {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (hn : ∀ i, d i ≤ d n) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hS : Feasible r d l σ s) :
    ∀ i, σ.symm n < σ.symm i → r i ≤ s n + l n := by sorry

end GTWSched.MaxDisc
