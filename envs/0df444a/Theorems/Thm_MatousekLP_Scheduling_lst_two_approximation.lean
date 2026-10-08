-- Prove2me | Theorems.Thm_MatousekLP_Scheduling_lst_two_approximation
-- name    : MatousekLP.Scheduling.lst_two_approximation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:40:19.581045+00:00
-- url     : https://prove2.me/theorems/4bbad9f0-2ee5-4174-84da-e21c79ce938f
-- title:
--   Theorem 8.3.4 — LP rounding schedules unrelated machines within twice the optimal makespan
-- statement:
--   Let $n$ jobs be scheduled on $m$ machines, job $j$ taking time $d_{ij} > 0$ on machine $i$, and let $t_{\mathrm{opt}}$ be the makespan of an optimal schedule $\sigma_{\mathrm{opt}}$. For $T \in \mathbb{R}$ let $t^*(T)$ be the optimal value of the linear program $\mathrm{LPR}(T)$, with $t^*(T) = \infty$ when it is infeasible. Let $T^*$ minimize $t^*(T) + T$ over all real $T$, and let $(t^*, x^*)$ be an optimal solution of $\mathrm{LPR}(T^*)$ satisfying Assumption 8.3.1 (for instance a basic optimal solution).
--
--   Then the rounding of Lemma 8.3.3 applied to $x^*$ yields a schedule $\sigma$ that assigns each job $j$ to a machine with $x^*_{\sigma(j)\,j} > 0$ and whose makespan is at most twice the optimum:
--   $$
--   \max_{i} \sum_{j:\ \sigma(j) = i} d_{ij} \;\le\; 2\, t_{\mathrm{opt}} .
--   $$
--
--   This is the 2-approximation algorithm of Lenstra, Shmoys and Tardos (1990) for minimizing the makespan on unrelated parallel machines, an NP-hard problem.
--
--   **Formalization Note** "The algorithm in the proof of Lemma 8.3.3 computes a schedule" is formalized by the property of that schedule: it uses only edges of the support graph of $x^*$ ($x^*_{\sigma(j) j} > 0$). Without this constraint the conclusion would be trivial, since $\sigma_{\mathrm{opt}}$ itself has makespan $t_{\mathrm{opt}} \le 2 t_{\mathrm{opt}}$. Minimality of $T^*$ is the hypothesis $t^* + T^* \le t + T$ for every real $T$ and every optimal solution $(t, x)$ of $\mathrm{LPR}(T)$. The running time of the algorithm is not formalized. Machines are `Fin m`, jobs `Fin n`.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 155, Theorem 8.3.4

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_MatousekLP_Scheduling_LPRelaxation

namespace MatousekLP.Scheduling

/-- Theorem 8.3.4 (Matoušek–Gärtner, p. 155; Lenstra–Shmoys–Tardos). Let `T*` minimize
`t*(T) + T` over all real `T` (with `t*(T) = ∞` when `LPR(T)` is infeasible), and let
`(t*, x*)` be an optimal solution of `LPR(T*)` satisfying Assumption 8.3.1. Then the
rounding of Lemma 8.3.3 yields a schedule `σ` that assigns every job `j` along an edge of
the support graph (`x*_{σ(j) j} > 0`) and has makespan at most `2 t_opt`, where `t_opt`
is the makespan of an optimal schedule `σopt`. -/
theorem lst_two_approximation {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (hd : ∀ i j, 0 < d i j) (σopt : Fin n → Fin m) (hσopt : IsOptimalSchedule d σopt)
    (Tstar tstar : ℝ) (xstar : Matrix (Fin m) (Fin n) ℝ)
    (hopt : LPROptimal d Tstar tstar xstar) (hA : Assumption831 d Tstar xstar)
    (hmin : ∀ (T t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ),
      LPROptimal d T t x → tstar + Tstar ≤ t + T) :
    ∃ σ : Fin n → Fin m, (∀ j, 0 < xstar (σ j) j) ∧
      makespan d σ ≤ 2 * makespan d σopt := by sorry

end MatousekLP.Scheduling
