-- Prove2me | Theorems.Thm_MatroidEquitability_Supplement_theorem_18
-- name    : MatroidEquitability.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:27:12.333447+00:00
-- url     : https://prove2.me/theorems/ab84eb13-50a0-4d09-a7a4-4d444dff3a3f
-- title:
--   Theorem 18 — the network of Figure 2 disproves the Morell–Skutella conjecture
-- statement:
--   Let $k\ge4$ and let $N_k$ be the network of Figure 2 with its demands $d$ and its fractional flow $x$. Then:
--
--   1. $N_k$ is acyclic and all its demands are positive;
--   2. $x$ satisfies the demands;
--   3. $\max_j d_j=8k$;
--   4. every unsplittable flow $y$ in $N_k$ satisfies
--   $$\max_a|x_a-y_a|\ \ge\ 9k-3=\Bigl(\frac98-\frac3{8k}\Bigr)\cdot\max_j d_j ;$$
--   5. $9k-3>8k=\max_jd_j$.
--
--   So no unsplittable flow meets the bound $|x_a-y_a|\le\max_jd_j$ of the Morell–Skutella conjecture (Conjecture 5): $N_k$ is a counterexample.
--
--   The conjecture was proved for divisible demands and for acyclic planar digraphs; this instance shows that the additive error $\max_j d_j$ cannot be achieved in general, and that a factor of at least $9/8-o(1)$ is needed.
--
--   **Formalization Note** The maximum over the finitely many arcs is stated as the existence of an arc with $|x_a-y_a|\ge9k-3$, and $\max_jd_j=8k$ as "$8k$ is the greatest demand". Terminals are indexed by their names in the figure rather than by $[n]$.
--
--   Differences from the source:
--   - reading: the $2k$ arcs of flow $4k+4$ drawn into the block of $k+1$ central terminals → arcs into one undrawn hub vertex $h$, with an arc $h\to C_j$ of flow $8k$ to each central terminal; reason: without a hub the drawn flow cannot satisfy the demands ($8k$ is not a sum of whole arcs of flow $4k+4$), and the proof's first step needs every $s$-path to a central terminal to share its $4k+4$ arc; the arcs $h\to C_j$ carry exactly $8k$ in every unsplittable flow, so they add no deviation.
--   - encoding: "is a counterexample to Conjecture 5" → acyclicity, positive demands, $x$ satisfies the demands, and $9k-3>8k$; reason: these are the conjecture's hypotheses and the failure of its conclusion.
--   - encoding: terminals $t_1,\dots,t_n$ → a finite type of named terminals; $\max_a$, $\max_j$ → an existential and `IsGreatest`; reason: Lean convention, same instance.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Theorem 18 and Figure 2, p.20 (PDF p.22); proof pp.20–21 (PDF pp.22–23); Conjecture 5, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_MatroidEquitability_Supplement_UnsplittableFlow
import Definitions.Def_MatroidEquitability_Supplement_Figure2

namespace MatroidEquitability

namespace Supplement

/-- **Theorem 18** (printed p.20 = PDF p.22 of Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and
Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)): for each `k ≥ 4`,
the construction of Figure 2 is a counterexample to the Morell–Skutella Conjecture 5 with
`max_j d_j = 8k`, and every unsplittable flow `y` has `max_a |x_a − y_a| ≥ 9k − 3 = (9/8 − 3/(8k))·max_j d_j`.

The conclusion lists: `N_k` is acyclic; all demands are positive; the flow `x` of Figure 2 satisfies the
demands; `max_j d_j = 8k`; every unsplittable flow `y` has an arc `a` with `|x_a − y_a| ≥ 9k − 3`; the
identity `9k − 3 = (9/8 − 3/(8k))·8k`; and `9k − 3 > 8k`, so no unsplittable flow meets Conjecture 5's
bound `max_j d_j`.

**Formalization Note.** `N_k` is `figure2 k`, read from Figure 2 with an undrawn hub vertex collecting
the `2k` arcs of flow `4k + 4` and forwarding `8k` to each of the `k + 1` central terminals (see
`Fig2Vertex`). `max_a` over the finite nonempty arc set is expressed as the existence of an arc. -/
theorem theorem_18 (k : ℕ) (hk : 4 ≤ k) :
    (figure2 k).IsAcyclic ∧
      (∀ j, 0 < (figure2 k).demand j) ∧
      (figure2 k).SatisfiesDemands (figure2Flow k) ∧
      IsGreatest (Set.range (figure2 k).demand) (8 * k) ∧
      (∀ y : Fig2Arc k → ℝ, (figure2 k).IsUnsplittable y →
        ∃ a, (9 * k - 3 : ℝ) ≤ |figure2Flow k a - y a|) ∧
      (9 * k - 3 : ℝ) = (9 / 8 - 3 / (8 * k)) * (8 * k) ∧
      (8 * k : ℝ) < 9 * k - 3 := by sorry

end Supplement

end MatroidEquitability
