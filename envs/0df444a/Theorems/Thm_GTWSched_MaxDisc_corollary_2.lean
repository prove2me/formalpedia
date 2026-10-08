-- Prove2me | Theorems.Thm_GTWSched_MaxDisc_corollary_2
-- name    : GTWSched.MaxDisc.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:04:44.675026+00:00
-- url     : https://prove2.me/theorems/f7ae7ffd-004e-40a8-ac06-0fb874d5602f
-- title:
--   COROLLARY 2, p. 344 — if a feasible schedule exists, some optimum schedule is in standard form and has the release time property
-- statement:
--   Let $N$ tasks on one processor have lengths $l_i \ge 0$, release times $r_i \ge 0$ and deadlines $d_i$ in special form for a constant $\alpha \ge 0$ (for every $i$, either $d_i - r_i = l_i + \alpha$, or $r_i = 0$ and $d_i < l_i + \alpha$), indexed so that $d_0 \le d_1 \le \dots \le d_{N-1}$; let $T_n$, $n = N - 1$, be the last task. If a feasible schedule exists, then there are an optimum schedule $(\sigma, s)$ and a split index $j$ such that
--
--   $$(\sigma, s) \text{ is in standard form with split index } j \text{ and has the release time property w.r.t. } T_n.$$
--
--   Standard form means: $0 \le j \le N - 1$; the schedule begins with an optimum schedule of the tasks of index $< j$; then comes $T_n$, starting at the maximum of $r_n$ and the completion time of that first part; then the tasks of index $j, \dots, N-2$ in this order, without idle time. The release time property means every task after $T_n$ has a release time strictly later than the start of $T_n$.
--
--   This is the statement the paper's algorithm for minimizing the maximum discrepancy is built on: an optimum schedule for a prefix of the tasks is found among the standard-form candidates, one per split index, built from optimum schedules of shorter prefixes.
--
--   **Formalization Note.** Indices are 0-based. The paper's dummy task $T_0$ ($r_0 = d_0 = l_0 = 0$) is not a task; an empty first part ($j = 0$) completes at time $0$. The split index $j$ is the number of real tasks before $T_N$, so its range $0 \le j \le N-1$ is the paper's. Ties among deadlines are allowed; the standard form is relative to the given sorted indexing.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 344, COROLLARY 2 (standard form and split index defined in the paragraph before it)

import Mathlib
import Definitions.Def_GTWSched_MaxDisc_Model

namespace GTWSched.MaxDisc

theorem corollary_2 {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (hd : Monotone d) (n : Fin N) (hnlast : n.val + 1 = N)
    (hfeas : ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ), Feasible r d l σ s) :
    ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) (j : ℕ),
      Optimum r d l σ s ∧ StandardForm r d l σ s j ∧ ReleaseTimeProperty r σ s n := by sorry

end GTWSched.MaxDisc
