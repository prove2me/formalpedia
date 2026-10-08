-- Prove2me | Theorems.Thm_MatousekLP_Codes_delsarte_bound
-- name    : MatousekLP.Codes.delsarte_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:13:46.684272+00:00
-- url     : https://prove2.me/theorems/36ca4ab7-be38-4375-bcc4-9865524641b1
-- title:
--   Theorem 8.4.3 (The Delsarte bound) — $A(n,d)$ is at most the optimum of the Delsarte linear program
-- statement:
--   For integers $0 \le i, t \le n$ let $K_t(n,i) = \sum_{j=0}^{\min(i,t)}(-1)^j\binom ij\binom{n-i}{t-j}$. Then for every $n$ and $d$, the maximum size $A(n,d)$ of a code $C \subseteq \{0,1\}^n$ with distance $d$ is bounded above by the optimum value of the linear program in variables $x_0,\dots,x_n$
--   $$
--   \begin{aligned}
--   \text{maximize}\quad & x_0 + x_1 + \dots + x_n\\
--   \text{subject to}\quad & x_0 = 1,\\
--   & x_i = 0, \quad i = 1,\dots,d-1,\\
--   & \textstyle\sum_{i=0}^n K_t(n,i)\, x_i \ge 0, \quad t = 1,\dots,n,\\
--   & x_0,\dots,x_n \ge 0.
--   \end{aligned}
--   $$
--   Equivalently: if a real number $v$ satisfies $x_0 + \dots + x_n \le v$ for every feasible solution $x$ of this program, then $A(n,d) \le v$.
--
--   This is the linear programming bound of Delsarte (1973); for example it gives $A(17,3) \le 6553$, against $7281$ from the sphere-packing bound.
--
--   **Formalization Note** The optimum value is not written as a real supremum (which Lean would set to $0$ on an empty or unbounded set); the theorem is stated against every upper bound $v$ of the objective on the feasible set, which is exactly "$A(n,d) \le$ optimum". The program is feasible ($x = (1,0,\dots,0)$), so any such $v$ is at least $1$ and the hypothesis is never vacuous.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, pp. 159–160, Theorem 8.4.3 (The Delsarte bound)

import Mathlib
import Definitions.Def_MatousekLP_Codes_Basic
import Definitions.Def_MatousekLP_Codes_DelsarteLP

open Finset

namespace MatousekLP.Codes

/-- Theorem 8.4.3 (The Delsarte bound), pp. 159–160: for every `n` and `d`, `A(n, d)` is
bounded above by the optimum value of the Delsarte linear program. Stated against every
upper bound `v` of the objective `x_0 + ⋯ + x_n` on the feasible set. -/
theorem delsarte_bound (n d : ℕ) (v : ℝ)
    (hv : ∀ x : Fin (n + 1) → ℝ, IsDelsarteFeasible n d x → delsarteObjective x ≤ v) :
    (A n d : ℝ) ≤ v := by sorry

end MatousekLP.Codes
