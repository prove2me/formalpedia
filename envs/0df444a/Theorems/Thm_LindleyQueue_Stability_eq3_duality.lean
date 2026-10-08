-- Prove2me | Theorems.Thm_LindleyQueue_Stability_eq3_duality
-- name    : LindleyQueue.Stability.eq3_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:33:20.698985+00:00
-- url     : https://prove2.me/theorems/89f08817-c9d5-442c-ab88-ef3d81b9b2f6
-- title:
--   Eq. (3) — $F_{r+1}(x) = p(U_s \le x \text{ for all } s \le r)$ for $x \ge 0$
-- statement:
--   In Lindley's single-server queue (Assumptions 1–2), let $F_{r+1}(x) = p(w_{r+1} \le x)$ be the waiting-time distribution function of the $(r+1)$th customer and $U_s = u_1 + \dots + u_s$ the random walk of the differences $u_s = s_s - t_s$. Then for every $r \ge 0$ and every $x \ge 0$,
--
--   $$
--   F_{r+1}(x) = p(U_s \le x \text{ for all } 1 \le s \le r).
--   $$
--
--   For $r = 0$ the event on the right is the sure event, matching $F_1(x) = 1$ for $x \ge 0$.
--
--   This identity connects the queue with a random walk with an absorbing barrier at $x$: the probability that the $(r+1)$th customer waits at most $x$ equals the probability that the walk has not crossed $x$ during its first $r$ steps. It is the identity on which the existence of the limit and the stability criterion rest.
--
--   **Formalization Note** Customers are numbered from $0$: `F r x` is the paper's $F_{r+1}(x)$, and the event is $\{\omega : U_n(\omega) \le x \text{ for } 1 \le n \le r\}$. The restriction $x \ge 0$ is the paper's ("for $x \ge 0$", p. 279); for $x < 0$ the left side is $0$ and the right side need not be. The identity is an equality of probabilities, not of events: the waiting time is a maximum of suffix sums $u_k + \dots + u_r$, and the passage to the prefix sums $U_s$ uses that the $u_r$ are i.i.d.
-- source:
--   Lindley (Proc. Camb. Phil. Soc. 48, 1952), §3, eq. (3), p. 279

import Mathlib
import Definitions.Def_LindleyQueue_Stability_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace LindleyQueue.Stability

/-- Eq. (3), p. 279: for `x ≥ 0`, `F_{r+1}(x) = p(U_s ≤ x for all 1 ≤ s ≤ r)`
(0-based: `F r` is the paper's `F_{r+1}`). -/
theorem eq3_duality {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Input Ω P) (r : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    Q.F r x = P.real {ω | ∀ n : ℕ, 1 ≤ n → n ≤ r → Q.U n ω ≤ x} := by sorry

end LindleyQueue.Stability
