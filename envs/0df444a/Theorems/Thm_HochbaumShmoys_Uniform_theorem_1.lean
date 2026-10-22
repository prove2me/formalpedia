-- Prove2me | Theorems.Thm_HochbaumShmoys_Uniform_theorem_1
-- name    : HochbaumShmoys.Uniform.theorem_1
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:28.814266+00:00
-- url     : https://prove2.me/theorems/e2ea7716-ab9d-474c-b068-454b131fa613
-- title:
--   Theorem 1 — binary search with an $\varepsilon/2$-relaxed procedure for $\log m+\log(3/\varepsilon)$ iterations is an $\varepsilon$-approximation (p. 541)
-- statement:
--   Let $\varepsilon>0$, let $m\ge1$ machines have speeds $s_i>0$ and $n$ jobs have processing times $p_j>0$, and let $D$ be any $\varepsilon/2$-relaxed decision procedure. Let $\sigma^\ast$ be the schedule output by the binary search of §2 driven by $D$, initialized with $U_0=\sum_jp_j/\max_is_i$, $L_0=\sum_jp_j/(m\max_is_i)$ and all jobs on a fastest machine, and run for $\lceil\log_2m+\log_2(3/\varepsilon)\rceil$ iterations. Then for every schedule $\tau$,
--   $$C_{\max}(\sigma^\ast)\le(1+\varepsilon)\,C_{\max}(\tau),$$
--   i.e. the output is within a factor $1+\varepsilon$ of the optimum makespan.
--
--   This reduces the approximation of $Q\|C_{\max}$ to the construction of relaxed decision procedures for bin packing with variable bin sizes (the dual approximation approach).
--
--   **Formalization Note** Stated as printed, for every $\varepsilon>0$. Finding F1: the statement is false for $\varepsilon=3$ ($m=8$ identical machines, $128$ jobs of size $1/16$: a valid $3/2$-relaxed procedure can lead to makespan $75/16>4=(1+\varepsilon)\cdot\mathrm{OPT}$); a disproof is a legitimate outcome. The corrected form with $\varepsilon\le1$ is a separate item. The optimum is expressed by comparison with every schedule $\tau$; the paper's "log" is base 2, rounded up.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 541, Theorem 1

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_HochbaumShmoys_Uniform_BinarySearch

namespace HochbaumShmoys.Uniform

theorem theorem_1 (ε : ℝ) (hε : 0 < ε) (m n : ℕ) (hm : 0 < m) (s : Fin m → ℝ)
    (p : Fin n → ℝ) (hs : ∀ i, 0 < s i) (hp : ∀ j, 0 < p j)
    (D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m))
    (hD : IsRelaxedDecisionProcedure (ε / 2) D) (τ : Fin n → Fin m) :
    makespan p s (binarySearch D p s hm (iterationCount m ε)) ≤
      (1 + ε) * makespan p s τ := by sorry

end HochbaumShmoys.Uniform
