-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_theorem_1_1
-- name    : MinCostArbPacking.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:15.89491+00:00
-- url     : https://prove2.me/theorems/203055f0-1596-4607-9b5b-e919a7d5de09
-- title:
--   Theorem 1.1 — minimum-cost $k$-arborescence packing in $O(km\log(kn)+k^2n\log n\log^2(kn)+k^4n\log^2(kn))$
-- statement:
--   **Theorem 1.1.** Let $n\ge2$. A minimum-cost packing of $k$ arc-disjoint $r$-arborescences, or a report that none exists, can be computed deterministically in
--
--   $$O\big(km\log(kn)+k^2n\log n\log^2(kn)+k^4n\log^2(kn)\big)\tag{1.1}$$
--
--   time for arbitrary real costs. For fixed $k$, this is $O(m\log n+n\log^3 n)$.
--
--   Formally: there are one program $P$ of the unit-cost real RAM and an absolute constant $C$ such that for every directed multigraph with $n\ge2$ vertices and $m$ arcs (parallel arcs, loops and arcs entering $r$ allowed), every root $r$, every integer $k\ge1$ and every cost vector $c\in\mathbb R^m$:
--
--   1. $P$ halts within $C$ times (1.1) steps, with $\log x=\max\{1,\log_2 x\}$;
--   2. it reports "none" exactly when $G$ has no $k$ arc-disjoint $r$-arborescences;
--   3. otherwise it outputs $k$ pairwise disjoint $r$-arborescences whose total cost is at most that of every such packing of $G$;
--   4. for every fixed $k\ge1$ there is $C_k$ such that the same program halts within $C_k(m\log n+n\log^3 n)$ steps on every input with that $k$.
--
--   The bound does not depend on the costs, and reals are accessed only by exact arithmetic and comparisons, so the algorithm is strongly polynomial.
--
--   Differences from the source:
--   - encoding: running time $O(f)$ in the model of §3.1 (exact arithmetic and comparisons in constant time) → one program of the unit-cost real RAM `Machine`, chosen before the input, halting within $C\cdot f$ executed instructions with an absolute constant $C$, for every word bound $W \ge (\mathrm{size}+2)^{c}$; reason: the standard reading of a deterministic time bound; the step count is intrinsic to the interpreter
--   - encoding: the output "a packing, or a report that none exists" → output cell 0 equal to 0 iff no packing exists, else 1 with $k(n-1)$ arc cells decoding to an optimal packing; reason: a total decoding of the final memory; copying the output is charged
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §1, p.1, Theorem 1.1 (proof §5.4, p.26)

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_IO
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Theorem 1.1, p.1. Let `n ≥ 2`. A minimum-cost packing of `k` arc-disjoint `r`-arborescences, or
a report that none exists, can be computed deterministically in
`O(km log(kn) + k² n log n log²(kn) + k⁴ n log²(kn))` time for arbitrary real costs; for fixed `k`
this is `O(m log n + n log³ n)`. One program of the unit-cost real RAM, fixed before the input, is
correct on every input with `n ≥ 2`, `k ≥ 1` (loops, parallel arcs and arcs entering `r` allowed,
real costs of any sign) and halts within `C` times the bound (1.1), `C` absolute; and for every
fixed `k` the same program halts within `C_k·(m log n + n log³ n)` steps. -/
theorem theorem_1_1 : ∃ (P : Machine.Program) (cw : ℕ) (C : ℝ),
    (∀ X : Instance, 2 ≤ X.n → 1 ≤ X.k → ∀ W : ℤ, ((X.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
      Machine.HaltsWithin P W X.inI X.inR (C * boundMain X) (fun o _ => PackingOutput X o)) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ Ck : ℝ, ∀ X : Instance, X.k = k → 2 ≤ X.n →
      ∀ W : ℤ, ((X.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
        Machine.HaltsWithin P W X.inI X.inR
          (Ck * ((X.m : ℝ) * logL X.n + X.n * logL X.n ^ 3)) (fun o _ => PackingOutput X o)) := by sorry

end MinCostArbPacking.Main
