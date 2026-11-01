-- Prove2me | Theorems.Thm_MultiIssueMediation_adjacent_strategyProof
-- name    : MultiIssueMediation.adjacent_strategyProof
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:11.853767+00:00
-- url     : https://prove2.me/theorems/ff48741a-9e44-48eb-a262-d47ceb418ee3
-- title:
--   Proof of Theorem 1, pp.30–31 — adjacent rules are strategy-proof (corrected: one common $y\ne o_Y$ in clause (i))
-- statement:
--   If $m\ge 2$ and $f$ is an adjacent rule, then $f$ is strategy-proof: neither negotiator can gain by misreporting, at any consistent ordering of the true type.
--
--   Differences from the source:
--   - correction: clause (i): f_{ℓ,j} = (o_X, y) for some y ∈ Y, cell by cell → one y ≠ o_Y common to all cells with ℓ < j; reason: the printed clause is false in the if direction: for m = 2, f_{1,1} = b_1, f_{2,2} = b_2, f_{2,1} = b_1, f_{1,2} = (o_X, o_Y) satisfies it, yet (o_X, y_1) dominates f_{1,2} by monotonicity, so f is not efficient; the proof (Part i, p.31) and Theorem 3 (p.21) have the corrected form
--   - reading: there exists a precedence order, printed inside "If ℓ > j" → one strict total order on B, quantified outside all cells; reason: per-cell existence would make the display empty and the if direction false (m = 3, f_{2,1} = b_1, f_{3,2} = b_2, f_{3,1} = b_2); Example 2 (p.16) and Step 2 (pp.34–37) use one global order
--   - reading: a consistent extension map Λ; Definition 1 constrains it from one side and Theorem 1 does not name it → Λ(θ_i) is the set of all consistent orderings (admissibleOrderings); reason: it is the only reading under which Theorem 1 is true (singleton maps give a counterexample at m = 3) and the one the proof uses, pp.28–29
--   - reading: there exists a one-to-one mapping t_i : X → Y → the fixed map t(x_k) = y_{m+1−k}, t(o_X) = o_Y, for both negotiators; reason: Example 1 (pp.13–14) and the definition of B (p.14) fix it; t(o_X) is never used
--   - encoding: types in Θ_i, m+1 positions of o_X → the m rows and m columns of the paper's matrix, indexed by Fin m; reason: the paper's own domain M × M (p.15), which leaves out the type that accepts nothing
--   - encoding: indices 1, …, m, outside options o_X, o_Y, cells f_{ℓ−1,j}, f_{ℓ,j+1} → Fin m with value = index − 1, Option (Fin m) with none the outside option, Fin.rev for m+1−k, indices p, q with p + 1 = ℓ, q = j + 1; reason: Lean conventions; the instances are the same
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, proof of Theorem 1, 'if' part, pp.30–31

import Mathlib
import Definitions.Def_MultiIssueMediation_AdjacentRule

namespace MultiIssueMediation

/-- An adjacent rule is strategy-proof, for both negotiators (Kesten, Özyurt, *Efficient and
Incentive Compatible Mediation: An Ordinal Market Design Approach*, working paper, 4 October 2018,
proof of Theorem 1, 'if' part, pp.30–31). The page treats negotiator 1 "without loss of
generality". -/
theorem adjacent_strategyProof {m : ℕ} (hm : 2 ≤ m) (f : MediationRule m)
    (hf : IsAdjacentRule f) : StrategyProof f := by sorry

end MultiIssueMediation
