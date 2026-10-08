-- Prove2me | Theorems.Thm_GTWSched_MaxDisc_rtp_implies_deadline_split
-- name    : GTWSched.MaxDisc.rtp_implies_deadline_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:49:45.951477+00:00
-- url     : https://prove2.me/theorems/adec58e6-246c-4d89-8857-570fb785df42
-- title:
--   Proof of COROLLARY 1, p. 344 — with the release time property, the tasks before T_N are those with deadline ≤ t + α
-- statement:
--   Let $N$ tasks have lengths $l_i \ge 0$, release times $r_i \ge 0$ and deadlines $d_i$ in special form for $\alpha \ge 0$ (for every $i$, either $d_i - r_i = l_i + \alpha$, or $r_i = 0$ and $d_i < l_i + \alpha$). Let $T_n$ be any task and take a feasible schedule with the release time property with respect to $T_n$; let $t = s_n$ be the starting time of $T_n$. Then for every task $T_i \neq T_n$,
--
--   $$T_i \text{ is executed before } T_n \iff d_i \le t + \alpha.$$
--
--   The paper observes that its proof of Corollary 1 shows exactly this: every optimum schedule with the release time property splits the tasks around $T_N$ by deadline, which is what the standard form and the algorithm of §3.2 exploit.
--
--   **Formalization Note.** The paper argues for optimum schedules with $T_N$ of maximum deadline; the statement here is for every feasible schedule and every task $T_n$, since the argument uses only feasibility, the special form and the release time property.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 344, proof of COROLLARY 1, and the remark "The proof of Corollary 1 actually showed that any optimum schedule with the release time property must have the form given in Corollary 1"

import Mathlib
import Definitions.Def_GTWSched_MaxDisc_Model

namespace GTWSched.MaxDisc

theorem rtp_implies_deadline_split {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hS : Feasible r d l σ s) (hrtp : ReleaseTimeProperty r σ s n) :
    ∀ i, i ≠ n → (σ.symm i < σ.symm n ↔ d i ≤ s n + α) := by sorry

end GTWSched.MaxDisc
