-- Prove2me | Theorems.Thm_MultiIssueMediation_theorem_1
-- name    : MultiIssueMediation.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:02.996476+00:00
-- url     : https://prove2.me/theorems/26bb1c9a-cb0a-411b-8a26-ee867f926cdc
-- title:
--   Theorem 1 — a mediation rule is efficient, individually rational and strategy-proof iff it is an adjacent rule (corrected: one common $y\ne o_Y$ in clause (i))
-- statement:
--   Two negotiators settle two issues with outcome sets $X=\{x_1,\dots,x_m,o_X\}$ and $Y=\{y_1,\dots,y_m,o_Y\}$, $m\ge 2$. Each negotiator's preferences over issue alternatives are diametrically opposed, $o_Y$ is worst for both, and the position of $o_X$ is private. Orderings over bundles are the consistent ones of Definition 1.
--
--   For every $m\ge2$, a mediation rule $f=[f_{\ell,j}]$ is efficient, individually rational and strategy-proof if and only if there are one $y\in Y\setminus\{o_Y\}$ and one complete, transitive and strict precedence order $\triangleright$ on the logrolling bundles $\mathbf B$ such that:
--
--   1. if $\ell<j$, then $f_{\ell,j}=(o_X,y)$;
--   2. if $\ell=j$, then $f_{\ell,j}=(x_\ell,y_{m+1-\ell})$;
--   3. (Adjacency) if $\ell>j$, then $f_{\ell,j}\in\{f_{\ell-1,j},f_{\ell,j+1}\}\subset\mathbf B$ and
--
--   $$f_{\ell,j}=\begin{cases} f_{\ell-1,j} & \text{if } f_{\ell-1,j}\triangleright f_{\ell,j+1},\\ f_{\ell,j+1} & \text{otherwise.}\end{cases}$$
--
--   The theorem characterizes all dominant-strategy mediation rules: with two issues and a public outside option in one of them, the impossibility of the single-issue case disappears, and every such rule is a fixed priority over the logrolling bundles.
--
--   Differences from the source:
--   - correction: clause (i): f_{ℓ,j} = (o_X, y) for some y ∈ Y, cell by cell → one y ≠ o_Y common to all cells with ℓ < j; reason: the printed clause is false in the if direction: for m = 2, f_{1,1} = b_1, f_{2,2} = b_2, f_{2,1} = b_1, f_{1,2} = (o_X, o_Y) satisfies it, yet (o_X, y_1) dominates f_{1,2} by monotonicity, so f is not efficient; the proof (Part i, p.31) and Theorem 3 (p.21) have the corrected form
--   - reading: there exists a precedence order, printed inside "If ℓ > j" → one strict total order on B, quantified outside all cells; reason: per-cell existence would make the display empty and the if direction false (m = 3, f_{2,1} = b_1, f_{3,2} = b_2, f_{3,1} = b_2); Example 2 (p.16) and Step 2 (pp.34–37) use one global order
--   - reading: a consistent extension map Λ; Definition 1 constrains it from one side and Theorem 1 does not name it → Λ(θ_i) is the set of all consistent orderings (admissibleOrderings); reason: it is the only reading under which Theorem 1 is true (singleton maps give a counterexample at m = 3) and the one the proof uses, pp.28–29
--   - reading: there exists a one-to-one mapping t_i : X → Y → the fixed map t(x_k) = y_{m+1−k}, t(o_X) = o_Y, for both negotiators; reason: Example 1 (pp.13–14) and the definition of B (p.14) fix it; t(o_X) is never used
--   - encoding: types in Θ_i, m+1 positions of o_X → the m rows and m columns of the paper's matrix, indexed by Fin m; reason: the paper's own domain M × M (p.15), which leaves out the type that accepts nothing
--   - encoding: indices 1, …, m, outside options o_X, o_Y, cells f_{ℓ−1,j}, f_{ℓ,j+1} → Fin m with value = index − 1, Option (Fin m) with none the outside option, Fin.rev for m+1−k, indices p, q with p + 1 = ℓ, q = j + 1; reason: Lean conventions; the instances are the same
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, Theorem 1, p.15

import Mathlib
import Definitions.Def_MultiIssueMediation_AdjacentRule

namespace MultiIssueMediation

/-- **Theorem 1** (Kesten, Özyurt, *Efficient and Incentive Compatible Mediation: An Ordinal Market
Design Approach*, working paper, 4 October 2018, Theorem 1, p.15): for every `m ≥ 2`, a mediation
rule `f` is efficient, individually rational and strategy-proof if and only if it is an adjacent
rule.

**Formalization Note.** `Λ` is the set of all consistent orderings; `IsAdjacentRule` has one
`y ≠ o_Y` in clause (i), corrected from the page, and one strict total order `▷` on `B`. Types are
the `m` rows and `m` columns of the paper's matrix, with `Fin m` values equal to paper indices minus
one and `none` the outside option. -/
theorem theorem_1 {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m) :
    Efficient f ∧ IndividuallyRational f ∧ StrategyProof f ↔ IsAdjacentRule f := by sorry

end MultiIssueMediation
