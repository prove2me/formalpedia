-- Prove2me | Theorems.Thm_GVRPricing_StoppingTime_prop4_lp_solution
-- name    : GVRPricing.StoppingTime.prop4_lp_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:46:54.936223+00:00
-- url     : https://prove2.me/theorems/225cbf20-711d-43be-9bdb-bad2c6c0b42a
-- title:
--   Proposition 4 — the discrete-price LP is solved by pricing at $p_{k^*}$ and $p_{k^*+1}$ only
-- statement:
--   Let a menu with $K\ge2$ prices be given, a stock $n\ge 0$ and a horizon $t>0$.
--
--   1. If $1\le k^*\le K-1$ and $\lambda_{k^*}t\ge n>\lambda_{k^*+1}t$, then the allocation with $t_j=0$ for $j\notin\{k^*,k^*+1\}$ and
--   $$t_{k^*}=\frac{n-\lambda_{k^*+1}t}{\lambda_{k^*}-\lambda_{k^*+1}},\qquad t_{k^*+1}=\frac{\lambda_{k^*}t-n}{\lambda_{k^*}-\lambda_{k^*+1}}$$
--   solves the linear program of §4.0.1.
--   2. ($k^*=0$) If $n>\lambda_1 t$, then $t_1=t$ and $t_j=0$ otherwise solves the LP.
--   3. ($k^*=K$) If $n\le\lambda_K t$, then $t_K=n/\lambda_K$ and $t_j=0$ otherwise solves the LP.
--
--   In every case $J^D(n,t)$ is the revenue of this allocation. This closed form is what makes the deterministic benchmark explicit and suggests the two-price stopping-time heuristic.
--
--   **Formalization Note** Lean indices are 0-based: the paper's $k^*$ is Lean's `k + 1`. The paper says "the solution", but the statement here is optimality only: when three menu points are collinear the optimum need not be unique. The statement relies on the menu's concavity condition (see the `Menu` definition), without which it is false.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1010 (PDF 12), Proposition 4

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_DetLP

namespace GVRPricing.StoppingTime

/-- Proposition 4 (p. 1010): closed-form solution of the discrete-price LP.  Indices are 0-based:
the paper's `k*` is `k + 1`, `λ_{k*}` is `M.lamN k`, and the edge cases `k* = 0`, `k* = K` are the
second and third clauses.  Stock `n ≥ 0`, horizon `t > 0` (standing assumptions of §2.2). -/
theorem prop4_lp_solution {K : ℕ} (M : Menu K) (n t : ℝ) (hn : 0 ≤ n) (ht : 0 < t) :
    (∀ k : ℕ, k + 1 < K → n ≤ M.lamN k * t → M.lamN (k + 1) * t < n →
        IsLPSolution M n t (twoPriceAlloc M k n t)) ∧
    (M.lamN 0 * t < n →
        IsLPSolution M n t (fun j => if j.val = 0 then t else 0)) ∧
    (n ≤ M.lamN (K - 1) * t →
        IsLPSolution M n t (fun j => if j.val = K - 1 then n / M.lamN (K - 1) else 0)) := by sorry

end GVRPricing.StoppingTime
