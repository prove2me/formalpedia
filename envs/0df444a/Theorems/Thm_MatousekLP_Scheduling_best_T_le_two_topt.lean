-- Prove2me | Theorems.Thm_MatousekLP_Scheduling_best_T_le_two_topt
-- name    : MatousekLP.Scheduling.best_T_le_two_topt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T12:40:03.892703+00:00
-- url     : https://prove2.me/theorems/45fb7552-e2c1-4775-b5f2-387963d5d830
-- title:
--   Proof of Theorem 8.3.4 — t*(T*) + T* ≤ 2 t_opt
-- statement:
--   Let $d_{ij} > 0$ be running times of $n$ jobs on $m$ machines, let $\sigma_{\mathrm{opt}}$ be an optimal schedule with makespan $t_{\mathrm{opt}}$, and write $t^*(T)$ for the optimal value of the linear program $\mathrm{LPR}(T)$ (with $t^*(T) = \infty$ when $\mathrm{LPR}(T)$ is infeasible). Let $T^*$ be a real number minimizing $t^*(T) + T$ over all real $T$, and let $(t^*, x^*)$ be an optimal solution of $\mathrm{LPR}(T^*)$. Then
--   $$
--   t^*(T^*) + T^* \le 2\, t_{\mathrm{opt}} .
--   $$
--
--   Combined with Lemma 8.3.3 at $T = T^*$, this bounds the makespan of the rounded schedule by twice the optimum.
--
--   **Formalization Note** Minimality of $T^*$ is the hypothesis $t^* + T^* \le t + T$ for every real $T$ and every optimal solution $(t, x)$ of $\mathrm{LPR}(T)$; values $T$ for which $\mathrm{LPR}(T)$ has no optimal solution impose no condition, matching the convention $t^*(T) = \infty$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 155, proof of Theorem 8.3.4 (displayed inequality); t*(T) = ∞ convention p. 154

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_MatousekLP_Scheduling_LPRelaxation

namespace MatousekLP.Scheduling

/-- Proof of Theorem 8.3.4 (Matoušek–Gärtner, p. 155): `t*(T*) + T* ≤ 2 t_opt`. Here
`t_opt` is the makespan of an optimal schedule, `T*` minimizes `t*(T) + T` over all
real `T` (with `t*(T) = ∞` when `LPR(T)` is infeasible), and `t* = t*(T*)` is the
value of an optimal solution of `LPR(T*)`. The minimality of `T*` is stated as
`t* + T* ≤ t + T` for every `T` and every optimal solution `(t, x)` of `LPR(T)`. -/
theorem best_T_le_two_topt {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ)
    (hd : ∀ i j, 0 < d i j) (σopt : Fin n → Fin m) (hσopt : IsOptimalSchedule d σopt)
    (Tstar tstar : ℝ) (xstar : Matrix (Fin m) (Fin n) ℝ)
    (hopt : LPROptimal d Tstar tstar xstar)
    (hmin : ∀ (T t : ℝ) (x : Matrix (Fin m) (Fin n) ℝ),
      LPROptimal d T t x → tstar + Tstar ≤ t + T) :
    tstar + Tstar ≤ 2 * makespan d σopt := by sorry

end MatousekLP.Scheduling
