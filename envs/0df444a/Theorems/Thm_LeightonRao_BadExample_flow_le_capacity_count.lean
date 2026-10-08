-- Prove2me | Theorems.Thm_LeightonRao_BadExample_flow_le_capacity_count
-- name    : LeightonRao.BadExample.flow_le_capacity_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:40.156884+00:00
-- url     : https://prove2.me/theorems/7b484c46-5f2a-4841-9d16-e51048fd3fe9
-- title:
--   §2.1, p. 794 — a uniform flow f on a 3-regular unit-capacity graph needs (1/2)(n choose 2)f(⌊log n⌋ − 2) ≤ 3n/2 capacity
-- statement:
--   Let $G$ be a 3-regular graph on $n\ge 8$ nodes with unit edge capacities, and write $\log$ for $\log_2$. If a concurrent flow of fraction $f$ for the uniform multicommodity flow problem on $G$ exists, then
--   $$\frac12\binom n2\,f\,\bigl(\lfloor\log n\rfloor-2\bigr)\ \le\ \frac{3n}{2}.$$
--   The left side is a lower bound on the capacity the flow uses (half of the commodities need paths of at least $\lfloor\log n\rfloor-2$ edges), and the right side is the total capacity of $G$.
--
--   This is the counting step that bounds the max-flow of the gap example.
--
--   **Formalization Note** The fraction $f$ is any real for which a feasible concurrent flow exists (for $f<0$ the inequality is trivial). Commodities are ordered pairs of demand $1/2$ (footnote 2, p. 791). The factor $\tfrac12$ in the display is the "at least half of the commodities", not the demand normalization. The paper's $\log n-2$ is stated with the floor $\lfloor\log n\rfloor-2$; $n\ge 8$ makes it at least $1$.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 794, §2.1, capacity display and the following sentence

import Mathlib
import Definitions.Def_LeightonRao_BadExample_Setting

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.BadExample

/-- §2.1, p. 794: a concurrent uniform flow of fraction `f` on a 3-regular unit-capacity
network with `n ≥ 8` nodes needs capacity `(1/2)(n choose 2) f (⌊log₂ n⌋ − 2)`, which is at
most the total capacity `3n/2`. -/
theorem flow_le_capacity_count {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3)
    (hn : 8 ≤ Fintype.card V)
    (f : V → V → V → V → ℝ) (lam : ℝ)
    (hf : IsConcurrentFlow (unitNetwork G) uniformDemand f lam) :
    lam * (1 / 2) * ((Fintype.card V).choose 2 : ℝ) *
        ((Nat.log 2 (Fintype.card V) : ℝ) - 2)
      ≤ 3 * (Fintype.card V : ℝ) / 2 := by sorry

end LeightonRao.BadExample
